import Liu.GreenDecay
import Liu.SourceParameter

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

theorem dbar_measurable (f : ℂ → ℂ) : Measurable (dbar f) := by
  have h1 := measurable_fderiv_apply_const ℝ f (1:ℂ)
  have hI := measurable_fderiv_apply_const ℝ f Complex.I
  unfold dbar
  fun_prop

private theorem pick_measurable {n : ℕ} (p : PickSum n) : Measurable p.value := by
  have h := p.power_measurable 1
  change Measurable (fun z => p.value z ^ ((1:ℝ):ℂ)) at h
  simpa using h

theorem PickSum.frozenError_measurable {n : ℕ} (p : PickSum n) (t : ℝ) :
    Measurable (p.frozenError t) ∧ Measurable (p.frozenErrorSlope t) := by
  have hv := pick_measurable p
  have hp := p.power_measurable t
  have hd := measurable_deriv (p.power (1+t))
  have hb := dbar_measurable (logInput p.value)
  have ha := dbar_measurable (logInput (p.power (1+t)))
  unfold PickSum.frozenError PickSum.frozenLogSource PickSum.frozenErrorSlope PickSum.parameterSlope
  constructor <;> fun_prop

/-- Uniform Green bounds for both the exact source defect and its parameter derivative. -/
theorem PickSum.frozenGreen_estimate {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ ρ ∈ ({p.frozenError t, p.frozenErrorSlope t} : Set (ℂ → ℂ)),
      ∀ z : ℂ, 0≤z.im → Integrable (fun w => (greenLog z w:ℂ)*ρ w) upperArea ∧
        ‖greenOperator ρ z‖ ≤ C*z.im/(1+‖z‖)^2 := by
  obtain ⟨A,hA,ha⟩ := p.frozen_source_error
  obtain ⟨B,hB,hb⟩ := p.frozenErrorSlope_bound
  obtain ⟨C,hC,h⟩ := green_log_quartic_estimate (show 0 ≤ max A B from hA.le.trans (le_max_left ..))
  refine ⟨C,hC,?_⟩
  intro t ht ρ hρ
  rcases hρ with rfl | hρ
  · apply h _ (p.frozenError_measurable t).1
    intro w hw
    apply (ha t ht w (le_of_lt hw)).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (le_max_left A B).trans (le_mul_of_one_le_right (hA.le.trans (le_max_left ..))
      (by linarith [log_nonneg (show 1≤2+‖w‖ by linarith [norm_nonneg w])]))
  · obtain rfl : ρ = p.frozenErrorSlope t := hρ
    apply h _ (p.frozenError_measurable t).2
    intro w hw
    apply (hb t ht w (le_of_lt hw)).trans
    gcongr
    · linarith [log_nonneg (show 1≤2+‖w‖ by linarith [norm_nonneg w])]
    · exact le_max_right ..

theorem greenOperator_measurable {ρ : ℂ → ℂ} (hm : Measurable ρ) : Measurable (greenOperator ρ) := by
  letI : SFinite upperArea := by unfold upperArea area; infer_instance
  have h : Measurable (fun q : ℂ × ℂ => (greenLog q.1 q.2:ℂ)*ρ q.2) := by
    unfold greenLog
    fun_prop
  unfold greenOperator
  exact (measurable_const (a:=(1/2:ℝ))).smul (h.stronglyMeasurable.integral_prod_right' (ν:=upperArea)).measurable

end Liu
