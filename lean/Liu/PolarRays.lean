module

public import Liu.FieldIntegral
public import Liu.RadialEnergy

@[expose] public section

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

def unitPhase (θ : ℝ) : ℂ := Complex.exp ((θ:ℂ)*Complex.I)
def polarRay (r θ : ℝ) : ℂ := (r:ℂ)*unitPhase θ

theorem unitPhase_norm (θ : ℝ) : ‖unitPhase θ‖=1 := Complex.norm_exp_ofReal_mul_I _

theorem polarRay_coord (p : ℝ×ℝ) : Complex.polarCoord.symm p = polarRay p.1 p.2 := by
  simp [Complex.polarCoord_symm_apply,polarRay,unitPhase,Complex.exp_mul_I]

private theorem ray_upper_iff {r θ : ℝ} (hr : 0<r) (hθ : θ∈Ioo (-π) π) :
    polarRay r θ∈upper ↔ 0<θ := by
  have hi : (polarRay r θ).im=r*sin θ := by simp [polarRay,unitPhase,Complex.exp_mul_I,←Complex.ofReal_sin,←Complex.ofReal_cos]
  change 0<(polarRay r θ).im ↔ _
  rw [hi,mul_pos_iff_of_pos_left hr]
  constructor
  · intro h
    by_contra! hc
    exact (not_lt_of_ge (sin_nonpos_of_nonpos_of_neg_pi_le hc hθ.1.le)) h
  · exact fun h => sin_pos_of_pos_of_lt_pi h hθ.2

private def rayDomain := Ioi (0:ℝ) ×ˢ Ioo (0:ℝ) π
private theorem rayDomain_m : MeasurableSet rayDomain := measurableSet_Ioi.prod measurableSet_Ioo
private theorem rayDomain_sub : rayDomain ⊆ polarCoord.target := fun v hv =>
  ⟨hv.1,lt_trans (by linarith [pi_pos] : -π<0) hv.2.1,hv.2.2⟩

private def rayValue (f : ℂ → ℂ) (v : ℝ×ℝ) := (v.1:ℂ)*f (polarRay v.1 v.2)

private theorem ray_integrable {f : ℂ → ℂ} (hm : Measurable f) (hi : Integrable f upperArea) :
    IntegrableOn (rayValue f) rayDomain (volume.prod volume) := by
  classical
  have hv : IntegrableOn f upper volume := by
    unfold upperArea area at hi
    rw [Measure.restrict_smul,integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0<1/π))
      ENNReal.ofReal_ne_top] at hi
    exact hi
  have hz := (integrable_indicator_iff upper_open.measurableSet).mpr hv
  have hF := hz.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hF
  rw [←Complex.lintegral_comp_polarCoord_symm (fun z => ‖upper.indicator f z‖ₑ)] at hF
  have hs := (lintegral_mono_set (μ:=volume) (f:=fun p : ℝ×ℝ => ENNReal.ofReal p.1 • ‖upper.indicator f (Complex.polarCoord.symm p)‖ₑ)
    rayDomain_sub).trans_lt hF
  have hme : Measurable (rayValue f) := by unfold rayValue polarRay unitPhase; fun_prop
  refine ⟨hme.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm,←Measure.volume_eq_prod]
  apply lt_of_eq_of_lt _ hs
  apply setLIntegral_congr_fun rayDomain_m
  intro p hp
  have hθ : p.2 ∈ Ioo (-π) π := (rayDomain_sub hp).2
  have hr : 0<p.1 := hp.1
  change ‖rayValue f p‖ₑ = ENNReal.ofReal p.1 • ‖upper.indicator f (Complex.polarCoord.symm p)‖ₑ
  rw [polarRay_coord,indicator_of_mem ((ray_upper_iff hr hθ).mpr hp.2.1)]
  simp [rayValue,enorm_mul,←ofReal_norm,abs_of_pos hr,smul_eq_mul,ENNReal.ofReal_mul hr.le]

/-- Polar coordinates for normalized upper-half-plane integrals with the ray
as the inner integral, including its almost-everywhere absolute convergence. -/
theorem upperArea_ray_integral {f : ℂ → ℂ} (hm : Measurable f) (hi : Integrable f upperArea) :
    (∀ᵐ θ ∂volume.restrict (Ioo (0:ℝ) π), IntegrableOn (fun r : ℝ => (r:ℂ)*f (polarRay r θ)) (Ioi 0)) ∧
    (∫ w, f w ∂upperArea) = (1/π:ℝ) • ∫ θ in Ioo (0:ℝ) π, ∫ r in Ioi (0:ℝ), (r:ℂ)*f (polarRay r θ) := by
  classical
  have h := ray_integrable hm hi
  change Integrable (rayValue f) ((volume.prod volume).restrict (Ioi (0:ℝ) ×ˢ Ioo (0:ℝ) π)) at h
  rw [←Measure.prod_restrict] at h
  refine ⟨h.prod_left_ae,?_⟩
  unfold upperArea area
  rw [Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),
    ←integral_indicator upper_open.measurableSet,←Complex.integral_comp_polarCoord_symm]
  congr 1
  change _ = ∫ θ in Ioo (0:ℝ) π, ∫ r in Ioi (0:ℝ), rayValue f (r,θ)
  rw [←integral_prod_symm (rayValue f) h,Measure.prod_restrict,←Measure.volume_eq_prod]
  change _=∫ p in rayDomain, rayValue f p
  rw [←inter_eq_right.mpr rayDomain_sub,←setIntegral_indicator rayDomain_m]
  apply setIntegral_congr_fun (s:=polarCoord.target) polarCoord.open_target.measurableSet
  intro v hv
  change v.1 • upper.indicator f (Complex.polarCoord.symm v) = _
  rw [polarRay_coord]
  have hr : 0<v.1 := hv.1
  have hθ : v.2 ∈ Ioo (-π) π := hv.2
  by_cases hpos : 0<v.2
  · rw [indicator_of_mem ((ray_upper_iff hr hθ).mpr hpos),
      indicator_of_mem (show v∈rayDomain from ⟨hr,hpos,hθ.2⟩)]
    rfl
  · rw [indicator_of_notMem (mt (ray_upper_iff hr hθ).mp hpos),
      indicator_of_notMem (show v∉rayDomain from fun hh => hpos hh.2.1),smul_zero]

end Liu
