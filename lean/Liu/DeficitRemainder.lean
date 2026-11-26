import Liu.AngularDeficit

noncomputable section
open Set MeasureTheory Filter Metric Real
open scoped Topology
namespace Liu

def finitePartRemainder (S : ℂ → ℂ) (m : ℝ) (z : ℂ) : ℝ :=
  (k₀*‖S z‖^2-‖field S z‖^2) - leadingDeficit m z

theorem leadingDeficit_integrableOn (m R : ℝ) :
    IntegrableOn (leadingDeficit m) (halfDisc R) area := by
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  let K := m^2*(k₀+(3*π/2)^2)
  have hK : IntegrableOn (fun _ : ℂ => K) (halfDisc R) area :=
    (integrableOn_const (s:=ball (0:ℂ) R) (μ:=area) (measure_ball_lt_top ..).ne).mono_set inter_subset_right
  have hrad : Measurable (radialTail 2) := by
    unfold radialTail
    apply Measurable.ite (measurableSet_lt measurable_const measurable_norm) (by fun_prop) measurable_const
  have hm : Measurable (leadingDeficit m) := by unfold leadingDeficit angularDeficit; fun_prop
  apply hK.mono' hm.aestronglyMeasurable
  filter_upwards with z
  have hπ := pi_pos
  have hk : 0 ≤ k₀ := by unfold k₀; positivity
  have hθ := Complex.abs_arg_le_pi z
  have ha : |π/2-z.arg| ≤ 3*π/2 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hθ
    apply abs_le.mpr; constructor <;> linarith
  have hang : |angularDeficit z.arg| ≤ k₀+(3*π/2)^2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg _) ha 2
    rw [sq_abs] at hs
    unfold angularDeficit
    apply abs_le.mpr; constructor <;> nlinarith [sq_nonneg (π/2-z.arg),sq_nonneg (3*π/2)]
  have hrt : |radialTail 2 z| ≤ 1 := by
    by_cases h : 1 < ‖z‖
    · simp only [radialTail,if_pos h,abs_of_nonneg (rpow_nonneg (norm_nonneg _) _)]
      exact rpow_le_one_of_one_le_of_nonpos h.le (by norm_num)
    · simp [radialTail,h]
  simp only [leadingDeficit,Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg m)]
  dsimp only [K]
  calc
    _ ≤ (m^2*1)*(k₀+(3*π/2)^2) := mul_le_mul (mul_le_mul_of_nonneg_left hrt (sq_nonneg _)) hang
      (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- A single absolute integrability estimate on the remainder suffices for the
radial finite part. Angular cancellation is already checked for each actual half-disc. -/
theorem finitePart_of_integrable_remainder {S : ℂ → ℂ} {m : ℝ}
    (hr : Integrable (finitePartRemainder S m) upperArea) :
    finitePartExists S ∧ deficit S = ∫ z, finitePartRemainder S m z ∂upperArea := by
  have hrem (R : ℝ) : IntegrableOn (finitePartRemainder S m) (halfDisc R) area :=
    (show IntegrableOn _ upper area from hr).mono_set inter_subset_left
  have he (z : ℂ) : k₀*‖S z‖^2-‖field S z‖^2 = finitePartRemainder S m z+leadingDeficit m z := by
    simp [finitePartRemainder]
  have hi (R : ℝ) : truncatedDeficit S R = ∫ z in halfDisc R, finitePartRemainder S m z ∂area := by
    unfold truncatedDeficit
    simp_rw [he,integral_add (hrem R) (leadingDeficit_integrableOn m R),halfDisc_leadingDeficit,add_zero]
  have ht : Tendsto (truncatedDeficit S) atTop (𝓝 (∫ z, finitePartRemainder S m z ∂upperArea)) := by
    exact (halfDisc_integral_limit hr).congr (fun R => (hi R).symm)
  refine ⟨⟨fun R _ => ?_,⟨_,ht⟩⟩,ht.limUnder_eq⟩
  simp_rw [he]
  exact (hrem R).add (leadingDeficit_integrableOn m R)

end Liu
