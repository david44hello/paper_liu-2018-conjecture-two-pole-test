import Liu.RayAngles
import Liu.SourceTailComparison
import Liu.FarDeficit
import Liu.ClosedGreen

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate
namespace Liu

def radialKernel (z w : ℂ) := greenResolvent z w/((‖w‖:ℂ)^2)

private theorem radialKernel_on_ray {z : ℂ} (hn : z≠0) (φ : ℝ) {r : ℝ} (hr : 0<r) :
    (r:ℂ)*radialKernel z (polarRay r φ) =
      z⁻¹*(((1+(r:ℂ)*(-conj (unitPhase φ)/z))⁻¹-
        (1+(r:ℂ)*(-unitPhase φ/z))⁻¹)/(r:ℂ)) := by
  have hnorm : ‖polarRay r φ‖=r := by rw [polarRay,norm_mul,Complex.norm_of_nonneg hr.le,unitPhase_norm,mul_one]
  unfold radialKernel
  rw [hnorm]
  simp only [greenResolvent,polarRay,map_mul,Complex.conj_ofReal]
  have eqn (u : ℂ) : 1+(r:ℂ)*(-u/z)=(z-(r:ℂ)*u)/z := by field_simp [hn]; ring
  rw [eqn,eqn]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  field_simp [hn,Complex.ofReal_ne_zero.mpr hr.ne'] <;> ring

private theorem angle_jump_interior {θ : ℝ} (hθ : θ∈Ioo (0:ℝ) π) :
    (∫ φ in Ioo (0:ℝ) π, (if φ<θ then φ else φ-π))=π*(θ-π/2) := by
  let f := fun φ : ℝ => if φ<θ then φ else φ-π
  have hm : Measurable f := Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_id (by fun_prop)
  have he : ∀ φ ∈ Ioo (0:ℝ) π, f φ = φ-(Ico θ π).indicator (fun _ => π) φ := by
    intro φ hφ
    by_cases hh : φ<θ
    · simp [f,hh,show φ∉Ico θ π from fun h => hh.not_ge h.1]
    · simp [f,hh,show φ∈Ico θ π from ⟨le_of_not_gt hh,hφ.2⟩]
  change (∫ φ in Ioo (0:ℝ) π, f φ) = _
  have hi : IntegrableOn (fun φ : ℝ => φ) (Ioo 0 π) := (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hj : Integrable ((Ico θ π).indicator (fun _ => π)) volume :=
    (integrable_indicator_iff measurableSet_Ico).mpr (integrableOn_const measure_Ico_lt_top.ne)
  rw [setIntegral_congr_fun measurableSet_Ioo he,integral_sub hi hj.restrict,setIntegral_indicator measurableSet_Ico,
    inter_eq_right.mpr (show Ico θ π ⊆ Ioo 0 π from fun x hx => ⟨hθ.1.trans_le hx.1,hx.2⟩),
    setIntegral_const,Real.volume_real_Ico_of_le hθ.2.le,smul_eq_mul,←integral_Ioc_eq_integral_Ioo,
    ←intervalIntegral.integral_of_le pi_pos.le,integral_id]
  ring

private theorem angle_jump_integral {θ : ℝ} (hθ : θ∈Icc (0:ℝ) π) :
    (∫ φ in Ioo (0:ℝ) π, (if φ<θ then φ else φ-π))=π*(θ-π/2) := by
  have hi : IntegrableOn (fun φ : ℝ => φ) (Ioo 0 π) := (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rcases hθ.1.eq_or_lt with he | hlo
  · subst θ
    rw [setIntegral_congr_fun (s:=Ioo (0:ℝ) π) measurableSet_Ioo (g:=fun φ => φ-π) (fun φ hφ => if_neg (not_lt.mpr hφ.1.le)),
      integral_sub hi (integrableOn_const measure_Ioo_lt_top.ne),setIntegral_const,Real.volume_real_Ioo_of_le pi_pos.le,
      smul_eq_mul,←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le pi_pos.le,integral_id]
    ring
  rcases hθ.2.eq_or_lt with he | hup
  · subst θ
    rw [setIntegral_congr_fun (s:=Ioo (0:ℝ) π) measurableSet_Ioo (g:=fun φ => φ) (fun φ hφ => if_pos hφ.2),
      ←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le pi_pos.le,integral_id]
    ring
  exact angle_jump_interior ⟨hlo,hup⟩

/-- Exact model derivative, evaluated by radial integration and the jump of
the two principal logarithms at the observation angle. -/
theorem radialKernel_integral {z : ℂ} (hz : 0≤z.im) (hn : z≠0) (hi : Integrable (radialKernel z) upperArea) :
    (∫ w, radialKernel z w ∂upperArea) = (2*Complex.I)*((z.arg-π/2:ℝ):ℂ)/z := by
  have hm : Measurable (radialKernel z) := by unfold radialKernel greenResolvent; fun_prop
  obtain ⟨hir,hpolar⟩ := upperArea_ray_integral hm hi
  rw [hpolar]
  let μ := volume.restrict (Ioo (0:ℝ) π)
  let jump := fun φ : ℝ => if φ<z.arg then φ else φ-π
  have hpt : ∀ᵐ φ ∂μ, (∫ r in Ioi (0:ℝ), (r:ℂ)*radialKernel z (polarRay r φ)) =
      (z⁻¹*(2*Complex.I))*((jump φ:ℝ):ℂ) := by
    filter_upwards [hir,ae_restrict_mem (μ:=volume) measurableSet_Ioo,μ.ae_ne z.arg] with φ hfi hφ he
    let a := -conj (unitPhase φ)/z
    let b := -unitPhase φ/z
    let g := fun r : ℝ => ((1+(r:ℂ)*a)⁻¹-(1+(r:ℂ)*b)⁻¹)/(r:ℂ)
    have hG : IntegrableOn (fun r => z⁻¹*g r) (Ioi 0) :=
      hfi.congr_fun (fun r hr => radialKernel_on_ray hn φ hr) measurableSet_Ioi
    have hgi : IntegrableOn g (Ioi 0) := by
      change Integrable (fun r => g r) (volume.restrict (Ioi 0))
      have hc := hG.const_mul z
      simpa only [←mul_assoc,mul_inv_cancel₀ hn,one_mul] using hc
    obtain ⟨ha,hb,hLog⟩ := reflected_ray_logs hz hn hφ he
    rw [setIntegral_congr_fun measurableSet_Ioi (fun r (hr : r∈Ioi (0:ℝ)) => radialKernel_on_ray hn φ hr),integral_const_mul,
      log_ray_integral ha hb hgi,hLog]; dsimp only [jump]; ring
  rw [integral_congr_ae hpt,integral_const_mul,integral_complex_ofReal]
  change (1/π:ℝ) • ((z⁻¹*(2*Complex.I))*(((∫ φ in Ioo (0:ℝ) π, jump φ):ℝ):ℂ)) = _
  rw [show (∫ φ in Ioo (0:ℝ) π, jump φ) = _ from angle_jump_integral ⟨Complex.arg_nonneg_iff.mpr hz,Complex.arg_le_pi _⟩,Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr pi_ne_zero,hn] <;> ring

theorem PickSum.radial_field_comparison {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → 1<‖z‖ →
      Integrable (radialKernel z) upperArea ∧
      Integrable (fun w => greenResolvent z w*(source p.value w-radialSource p.mass w)) upperArea ∧
      (∫ w, ‖greenResolvent z w*(source p.value w-radialSource p.mass w)‖ ∂upperArea) ≤ C*(1+log ‖z‖)/‖z‖^2 := by
  let ρ := fun w => source p.value w-radialSource p.mass w
  have hm : Measurable ρ := p.source_measurable.sub (by unfold radialSource; fun_prop)
  obtain ⟨K,hK,hcomp⟩ := p.source_radial_comparison
  obtain ⟨C,hC,h⟩ := greenResolvent_radial_error hm hK hcomp
  refine ⟨C,hC,?_⟩
  intro z hz hr
  obtain ⟨hi,hbound⟩ := h z hz hr
  obtain ⟨hiS,hfield⟩ := p.field_integral_closed hz
  let c := Complex.I*(p.mass:ℂ)/2
  have hc : c≠0 := div_ne_zero (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr p.mass_pos.ne')) (by norm_num)
  have eqn (w : ℂ) : c*radialKernel z w = greenResolvent z w*source p.value w-greenResolvent z w*ρ w := by
    dsimp [c,ρ,radialKernel,radialSource]
    push_cast; ring
  have hmod : Integrable (fun w => c*radialKernel z w) upperArea := (hiS.sub hi).congr (ae_of_all _ fun w => (eqn w).symm)
  have hk : Integrable (radialKernel z) upperArea := by
    simpa only [←mul_assoc,inv_mul_cancel₀ hc,one_mul] using hmod.const_mul c⁻¹
  exact ⟨hk,hi,hbound⟩

theorem PickSum.field_far_estimate {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → 1<‖z‖ →
      ‖field p.value z-fieldFarModel p.mass z‖ ≤ C*(1+log ‖z‖)/‖z‖^2 := by
  obtain ⟨C,hC,h⟩ := p.radial_field_comparison
  refine ⟨C,hC,?_⟩
  intro z hz hr
  obtain ⟨hk,hi,hbound⟩ := h z hz hr
  obtain ⟨hiS,hfield⟩ := p.field_integral_closed hz
  let ρ := fun w => source p.value w-radialSource p.mass w
  let c := Complex.I*(p.mass:ℂ)/2
  have eqn (w : ℂ) : c*radialKernel z w = greenResolvent z w*source p.value w-greenResolvent z w*ρ w := by
    dsimp [c,ρ,radialKernel,radialSource]; push_cast; ring
  have hcalc := integral_congr_ae (μ:=upperArea) (ae_of_all _ eqn)
  rw [integral_const_mul,integral_sub hiS hi,radialKernel_integral hz (norm_pos_iff.mp (zero_lt_one.trans hr)) hk] at hcalc
  have he : -(c*((2*Complex.I)*((z.arg-π/2:ℝ):ℂ)/z))=fieldFarModel p.mass z := by
    dsimp [c,fieldFarModel]; push_cast; ring_nf; simp [Complex.I_sq]; ring
  rw [hfield,←he]
  have iden : -(∫ w, greenResolvent z w*source p.value w ∂upperArea) - -(c*((2*Complex.I)*((z.arg-π/2:ℝ):ℂ)/z)) =
      -(∫ w, greenResolvent z w*ρ w ∂upperArea) := by rw [hcalc]; ring
  rw [iden,norm_neg]
  exact (norm_integral_le_integral_norm _).trans hbound

theorem PickSum.finite_part {n : ℕ} (p : PickSum n) :
    finitePartExists p.value ∧ deficit p.value=∫ z, finitePartRemainder p.value p.mass z ∂upperArea := by
  obtain ⟨C,hC,h⟩ := p.field_far_estimate
  exact p.finitePart_of_field_asymptotic (T:=2) hC (fun z hz hr => h z (le_of_lt hz) (by linarith))

end Liu
