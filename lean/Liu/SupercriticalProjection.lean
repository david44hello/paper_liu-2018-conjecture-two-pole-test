module

public import Liu.SupercriticalEnergy
public import Liu.ProjectionKernel
public import Liu.Denominator

@[expose] public section

noncomputable section
open Set MeasureTheory Real
open scoped Topology ComplexConjugate
namespace Liu

private theorem memLp_conjugate {f : ℂ → ℂ} (hf : MemLp f 2 upperArea) :
    MemLp (fun z => conj (f z)) 2 upperArea :=
  hf.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (ae_of_all _ fun _ => (Complex.norm_conj _).symm)

theorem reflectedPotential_eq_twice_green (f : ℂ → ℂ) (z : ℂ) :
    reflectedPotential f z=2*greenOperator f z := by
  simp only [greenOperator,reflectedPotential,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  ring

theorem SupercriticalSource.energy_eq_green {f : ℂ → ℂ} {t : ℝ} (h : SupercriticalSource f t)
    (hd : DifferentiableOn ℝ f upper) : energy (canonicalField f)=4*greenPairing f f := by
  let F := canonicalField f
  let U := reflectedPotential f
  have hf := h.field_memLp
  have hsq : Integrable (fun z => conj (F z)*F z) upperArea := (memLp_conjugate hf).integrable_mul hf
  have hu (z : ℂ) (hz : z∈upper) := canonicalField_dbar h.green.quadratic hz (hd.differentiableAt (upper_open.mem_nhds hz))
  obtain ⟨K,hK,hq⟩ := h.green.decay
  obtain ⟨M,hM,hU⟩ := green_L1_bound h.green.integrable h.measurable hK hq
  have hUc := reflectedPotential_continuous_closed h.green.quadratic (fun z hz => (hU z (le_of_lt hz)).1)
  have hUm : AEStronglyMeasurable U upperArea :=
    (hUc.mono (show upper ⊆ {z : ℂ | 0≤z.im} from fun z hz => (show 0<z.im from hz).le)).aestronglyMeasurable upper_open.measurableSet
  have hprod : Integrable (fun z => conj (U z)*f z) upperArea := by
    apply (h.green.integrable.norm.const_mul M).mono' ((Complex.continuous_conj.comp_aestronglyMeasurable hUm).mul h.measurable.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    change ‖conj (U z)*f z‖ ≤ M*‖f z‖
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right ((norm_integral_le_integral_norm _).trans (hU z (le_of_lt hz)).2) (norm_nonneg _)
  have heq : (fun z => conj (U z)*dbar F z) =ᵐ[upperArea] (fun z => conj (U z)*f z) := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    rw [(hu z hz).2]
  obtain ⟨C,hC,hb⟩ := h.field_decay
  have he := h.green.field_pairing (canonicalField_continuous h.green.quadratic).continuousOn
    (fun z hz => (hu z hz).1.differentiableWithinAt) h.pos hC hb hsq (hprod.congr heq.symm)
  rw [integral_congr_ae heq] at he
  have hreal := congrArg Complex.re he
  rw [Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero] at hreal
  rw [energy_eq_integral hf,greenPairing]
  calc
    _ = ∫ z, (conj (F z)*F z).re ∂upperArea := by
      apply integral_congr_ae; filter_upwards with z
      rw [mul_comm,Complex.mul_conj',←Complex.ofReal_pow,Complex.ofReal_re]
    _ = _ := (integral_re hsq).trans (hreal.trans (by
      change 2*RCLike.re (∫ z, conj (U z)*f z ∂upperArea)=_
      rw [←integral_re hprod]
      rw [←integral_const_mul (2:ℝ),←integral_const_mul (4:ℝ)]
      apply integral_congr_ae; filter_upwards with z
      simp [U,reflectedPotential_eq_twice_green,Complex.mul_re,Complex.mul_im]; ring))

/-- The complex gradient of a bounded zero-boundary potential has zero Bergman
projection whenever it belongs to L². -/
theorem dirichlet_field_projection_zero {U F : ℂ → ℂ} {D : ℂ → ℂ →L[ℝ] ℂ}
    (hUc : ContinuousOn U {z : ℂ | 0≤z.im}) (dU : ∀ z ∈ upper, HasFDerivAt U (D z) z)
    (hgrad : ∀ z ∈ upper, F z= -(D z 1-Complex.I*D z Complex.I))
    (hbottom : ∀ x : ℝ, U x=0) {M : ℝ} (hM : 0≤M) (hU : ∀ z : ℂ, 0≤z.im → ‖U z‖≤M)
    (hF : MemLp F 2 upperArea) : project (asL2 F)=0 := by
  obtain ⟨g,hg,_,hrep,hpoint⟩ := projection_has_kernel hF
  have vanish (a : ℂ) (ha : a∈upper) : bergmanIntegral F a=0 := by
    let g := bergmanKernel a
    have hbelow : (conj a).im<0 := by simp; exact ha
    have hn (z : ℂ) (hz : 0≤z.im) : z-conj a≠0 := by
      intro he; have hh := congrArg Complex.im (sub_eq_zero.mp he); linarith
    have hc : ContinuousOn g {z : ℂ | 0≤z.im} := by
      intro z hz; change ContinuousWithinAt (fun w : ℂ => -((w-conj a)^2)⁻¹) _ z
      fun_prop (disch := first | exact pow_ne_zero 2 (hn z hz) | exact hn z hz)
    have hg' (z : ℂ) (hz : z∈upper) := (bergmanKernel_analytic ha).differentiableAt (upper_open.mem_nhds hz)
    have hdz (z : ℂ) (hz : z∈upper) : dbar g z=0 := by
      rw [dbar,(hg' z hz).hasDerivAt.complexToReal_fderiv.fderiv]
      simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,smul_eq_mul,mul_one]
      ring_nf <;> simp [Complex.I_sq] <;> ring
    let P := poleBound 1 (conj a)
    have hb (z : ℂ) (hz : 0≤z.im) : ‖g z‖ ≤ P^2/(1+‖z‖)^(1+(1:ℝ)) := by
      have hh := pow_le_pow_left₀ (norm_nonneg _) (pole_global_decay (a:=1) (by norm_num) hbelow hz) 2
      norm_num only [one_add_one_eq_two,rpow_ofNat]
      simpa [g,bergmanKernel,pole,P,div_pow] using hh
    have hzero : (fun z => conj (U z)*dbar g z) =ᵐ[upperArea] 0 := by
      filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
      simp [hdz z hz]
    have hi : Integrable (fun z => conj (F z)*g z) upperArea := (memLp_conjugate hF).integrable_mul (bergmanKernel_memLp ha)
    have he := dirichlet_field_pairing hUc dU hgrad hbottom hM hU hc (fun z hz => ((hg' z hz).restrictScalars ℝ).differentiableWithinAt)
      zero_lt_one (sq_nonneg _) hb hi (integrable_zero _ _ _ |>.congr hzero.symm)
    rw [integral_congr_ae hzero] at he
    simp only [Pi.zero_apply,integral_zero,mul_zero] at he
    have hh := congrArg (starRingEnd ℂ) he
    rw [←integral_conj] at hh
    simpa [bergmanIntegral,g,map_mul] using hh
  rw [asL2,dif_pos hF,hrep]
  apply Lp.ext
  filter_upwards [hg.coeFn_toLp,Lp.coeFn_zero ℂ 2 upperArea,ae_restrict_mem (μ:=area) upper_open.measurableSet] with z he hzero hz
  simpa only [he,hzero,Pi.zero_apply,hpoint hz] using vanish z hz

theorem SupercriticalSource.projection_zero {f : ℂ → ℂ} {t : ℝ} (h : SupercriticalSource f t) :
    project (asL2 (canonicalField f))=0 := by
  obtain ⟨K,hK,hq⟩ := h.green.decay
  obtain ⟨M,hM,hU⟩ := green_L1_bound h.green.integrable h.measurable hK hq
  have hiU (z : ℂ) (hz : z∈upper) := (hU z (le_of_lt hz)).1
  exact dirichlet_field_projection_zero (reflectedPotential_continuous_closed h.green.quadratic hiU)
    (fun _ hz => reflectedPotential_hasFDerivAt h.measurable hK hq hiU hz)
    (fun _ hz => canonicalField_from_differential h.green.quadratic (le_of_lt hz))
    (reflectedPotential_boundary f) hM (fun z hz => (norm_integral_le_integral_norm _).trans (hU z hz).2) h.field_memLp

/-- The projection formula for classical primitives. -/
theorem SupercriticalSource.residual_eq_field {f h : ℂ → ℂ} {t : ℝ} (hf : SupercriticalSource f t)
    (df : DifferentiableOn ℝ f upper) (hh : MemLp h 2 upperArea) (dh : DifferentiableOn ℝ h upper)
    (hr : EqOn (dbar h) f upper) :
    asL2 h-project (asL2 h)=asL2 (canonicalField f) := by
  let F := canonicalField f
  have hF := hf.field_memLp
  have da : DifferentiableOn ℂ (h-F) upper := fun z hz =>
    (canonicalField_holomorphic_difference hf.green.quadratic hz (df.differentiableAt (upper_open.mem_nhds hz))
      (dh.differentiableAt (upper_open.mem_nhds hz)) (hr hz)).differentiableWithinAt
  have he := project_fixes_analytic (hh.sub hF) da
  have hz := hf.projection_zero
  simp only [asL2,dif_pos hF] at hz
  simp only [MemLp.toLp_sub hh hF,map_sub,hz,sub_zero] at he
  simp only [asL2,dif_pos hh,dif_pos hF]
  rw [he]; abel

end Liu
