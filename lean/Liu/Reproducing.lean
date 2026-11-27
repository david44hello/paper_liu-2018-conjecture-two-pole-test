module

public import Liu.DiscIntegral
public import Liu.BergmanClosed

@[expose] public section

noncomputable section
open Set MeasureTheory Metric Real
open scoped ComplexConjugate
namespace Liu

def bergmanKernel (z w : ℂ) : ℂ := -((w-conj z)^2)⁻¹

private theorem jac_nonzero {z : ℂ} (hz : z ∈ upper) {w : ℂ} (hw : w ∈ disc) : cayleyJac z w ≠ 0 := by
  have hn : z-conj z ≠ 0 := fun h => by
    have hh := congrArg Complex.im (sub_eq_zero.mp h); simp at hh; change 0<z.im at hz; linarith
  have hd : 1-w ≠ 0 := fun he => by rw [←sub_eq_zero.mp he] at hw; simpa [disc] using hw
  exact div_ne_zero hn (pow_ne_zero 2 hd)

theorem cayleyPull_kernel {z : ℂ} (hz : z ∈ upper) {w : ℂ} (hw : w ∈ disc) :
    cayleyPull z (bergmanKernel z) w = -(z-conj z)⁻¹ := by
  have hn : z-conj z ≠ 0 := fun h => by
    have hh := congrArg Complex.im (sub_eq_zero.mp h); simp at hh; change 0<z.im at hz; linarith
  have hd : 1-w ≠ 0 := fun he => by rw [←sub_eq_zero.mp he] at hw; simpa [disc] using hw
  have eqn : cayley z w-conj z = (z-conj z)/(1-w) := by unfold cayley; field_simp [hd]; ring
  simp only [cayleyPull,bergmanKernel,cayleyJac,eqn]
  field_simp [hn,hd]

theorem cayleyPull_normSq_integrable_iff {z : ℂ} (hz : z∈upper) (f : ℂ → ℂ) :
    Integrable (fun w => ‖f w‖^2) upperArea ↔ IntegrableOn (fun w => ‖cayleyPull z f w‖^2) disc area := by
  have h := cayley_integrable_iff hz (fun w => ‖f w‖^2)
  simpa only [upperArea,IntegrableOn,cayleyPull,norm_mul,mul_pow,smul_eq_mul,mul_comm] using h

theorem bergmanKernel_analytic {z : ℂ} (hz : z ∈ upper) : DifferentiableOn ℂ (bergmanKernel z) upper := by
  intro w hw
  have hn : w-conj z≠0 := fun h => by
    have hh := congrArg Complex.im (sub_eq_zero.mp h); simp at hh
    change 0<w.im at hw; change 0<z.im at hz; linarith
  unfold bergmanKernel
  fun_prop (disch := first | assumption | positivity)

theorem bergmanKernel_memLp {z : ℂ} (hz : z ∈ upper) : MemLp (bergmanKernel z) 2 upperArea := by
  have hm : Measurable (bergmanKernel z) := by unfold bergmanKernel; fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (cayleyPull_normSq_integrable_iff hz _).mpr
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  have h : IntegrableOn (fun _ : ℂ => ‖-(z-conj z)⁻¹‖^2) disc area :=
    integrableOn_const (measure_ball_lt_top ..).ne
  apply h.congr_fun _ Metric.isOpen_ball.measurableSet
  intro w hw
  dsimp only
  rw [cayleyPull_kernel hz hw]

theorem cayleyPull_holomorphic {z : ℂ} (hz : z ∈ upper) {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f upper) :
    DifferentiableOn ℂ (cayleyPull z f) disc := by
  have hκ : DifferentiableOn ℂ (cayley z) disc := fun w hw => (cayley_deriv z hw).differentiableAt.differentiableWithinAt
  have hJ : DifferentiableOn ℂ (cayleyJac z) disc := by
    intro w hw
    have h : 1-w≠0 := fun he => by rw [←sub_eq_zero.mp he] at hw; simpa [disc] using hw
    unfold cayleyJac
    fun_prop (disch := first | assumption | positivity)
  exact (hd.comp hκ (cayley_bijOn hz).mapsTo).mul hJ

/-- The half-plane evaluation kernel for analytic square-integrable functions, with dx dy/π. -/
theorem bergman_reproducing {f : ℂ → ℂ} (hf : MemLp f 2 upperArea) (hd : DifferentiableOn ℂ f upper)
    {z : ℂ} (hz : z ∈ upper) : (∫ w, f w*conj (bergmanKernel z w) ∂upperArea) = f z := by
  have hj := cayleyPull_holomorphic hz hd
  have hp2 := (cayleyPull_normSq_integrable_iff hz f).mp
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
  have hμ : AEStronglyMeasurable (cayleyPull z f) (area.restrict disc) :=
    hj.continuousOn.aestronglyMeasurable Metric.isOpen_ball.measurableSet
  have hp := (memLp_two_iff_integrable_sq_norm hμ).mpr hp2
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (area.restrict disc) := ⟨by rw [Measure.restrict_apply MeasurableSet.univ,univ_inter]; exact measure_ball_lt_top⟩
  have hm := disc_mean_integrable (hp.integrable (by norm_num)) hj
  rw [upperArea,cayley_area_integral hz]
  have heq (w : ℂ) (hw : w∈disc) : ‖cayleyJac z w‖^2 • (f (cayley z w)*conj (bergmanKernel z (cayley z w))) =
      cayleyPull z f w * conj (-(z-conj z)⁻¹) := by
    rw [←cayleyPull_kernel hz hw]
    simp only [cayleyPull,Complex.real_smul,Complex.ofReal_pow,←Complex.mul_conj',map_mul]
    ring
  rw [setIntegral_congr_fun (s:=disc) Metric.isOpen_ball.measurableSet heq,integral_mul_const,hm]
  have hn : z-conj z ≠ 0 := fun h => by
    have hh := congrArg Complex.im (sub_eq_zero.mp h); simp at hh; change 0<z.im at hz; linarith
  simp only [cayleyPull,cayley,cayleyJac,mul_zero,sub_zero,div_one,one_pow,map_neg,map_inv₀,map_sub,Complex.conj_conj]
  rw [show conj z-z = -(z-conj z) by ring,inv_neg,neg_neg]
  field_simp [hn]

end Liu
