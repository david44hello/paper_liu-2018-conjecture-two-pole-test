import Liu.Reproducing

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu

private theorem moment_bound {μ : Measure ℂ} {q g : ℂ → ℂ} (h : ∀ᵐ z ∂μ, ‖q z‖ < 1) (m : ℕ) :
    ∀ᵐ z ∂μ, ‖g z * q z^m‖ ≤ ‖g z‖ := by
  filter_upwards [h] with z hz
  rw [norm_mul,norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz.le)

theorem moments_integrable {μ : Measure ℂ} {q g : ℂ → ℂ} (hg : Integrable g μ) (hq : Measurable q)
    (h : ∀ᵐ z ∂μ, ‖q z‖ < 1) (m : ℕ) : Integrable (fun z => g z*q z^m) μ :=
  hg.norm.mono' (hg.aestronglyMeasurable.mul ((hq.pow_const m).aestronglyMeasurable)) (moment_bound h m)

theorem moments_vanish_at_infinity {μ : Measure ℂ} {q g : ℂ → ℂ} (hg : Integrable g μ)
    (hq : Measurable q) (h : ∀ᵐ z ∂μ, ‖q z‖ < 1) :
    Tendsto (fun m : ℕ => ∫ z, g z*q z^m ∂μ) atTop (𝓝 0) := by
  have H := tendsto_integral_of_dominated_convergence (μ:=μ) (F:=fun m z => g z*q z^m)
    (f:=fun _ => (0:ℂ)) (fun z => ‖g z‖) (fun m => (moments_integrable hg hq h m).aestronglyMeasurable)
    hg.norm (moment_bound h) (by
      filter_upwards [h] with z hz
      simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).const_mul (g z))
  simpa using H

/-- Dividing a density with zero analytic moments by a bounded geometric
resolvent preserves all its moments. Two applications give the Bergman kernel. -/
theorem vanishing_moments_div {μ : Measure ℂ} {q g : ℂ → ℂ} (hg : Integrable g μ)
    (hq : Measurable q) (h : ∀ᵐ z ∂μ, ‖q z‖ < 1) (hm : ∀ m : ℕ, ∫ z, g z*q z^m ∂μ = 0)
    {c : ℂ} (hc : ‖c‖<1) :
    Integrable (fun z => g z/(1-c*q z)) μ ∧
      ∀ m : ℕ, ∫ z, (g z/(1-c*q z))*q z^m ∂μ = 0 := by
  let G := fun z => g z/(1-c*q z)
  have hδ : 0<1-‖c‖ := sub_pos.mpr hc
  have sep : ∀ᵐ z ∂μ, 1-‖c‖ ≤ ‖1-c*q z‖ := by
    filter_upwards [h] with z hz
    have hn := norm_sub_norm_le (1:ℂ) (c*q z)
    rw [norm_one,norm_mul] at hn
    linarith [mul_le_of_le_one_right (norm_nonneg c) hz.le]
  have hmG : AEStronglyMeasurable G μ := by
    simp only [G,div_eq_mul_inv]
    exact hg.aestronglyMeasurable.mul ((measurable_const.sub (measurable_const.mul hq)).inv.aestronglyMeasurable)
  have hG : Integrable G μ := (hg.norm.div_const (1-‖c‖)).mono'
    hmG (by
      filter_upwards [sep] with z hz
      change ‖g z/(1-c*q z)‖ ≤ _
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hδ hz)
  let J := fun m : ℕ => ∫ z, G z*q z^m ∂μ
  have step (m : ℕ) : J m=c*J (m+1) := by
    have hi := moments_integrable hG hq h m
    have hi' := (moments_integrable hG hq h (m+1)).const_mul c
    have he : (∫ z, g z*q z^m ∂μ) = ∫ z, G z*q z^m-c*(G z*q z^(m+1)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [sep] with z hz
      have hne := norm_ne_zero_iff.mp (hδ.trans_le hz).ne'
      dsimp only [G]
      rw [pow_succ]; field_simp [hne]
    rw [hm,integral_sub hi hi',integral_const_mul] at he
    exact sub_eq_zero.mp he.symm
  refine ⟨hG,?_⟩
  intro m
  have repr (k : ℕ) : J m = c^k*J (k+m) := by
    induction k with
    | zero => simp
    | succ k ih => calc
        _ = c^k*J (k+m) := ih
        _ = c^(k+1)*J (k+1+m) := by rw [step (k+m),pow_succ]; rw [Nat.add_right_comm k m 1]; ring
  have hj : Tendsto (fun k : ℕ => J (k+m)) atTop (𝓝 0) := (moments_vanish_at_infinity hG hq h).comp (tendsto_add_atTop_nat m)
  have hp : Tendsto (fun k : ℕ => c^k*J (k+m)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc).mul hj
  exact tendsto_nhds_unique tendsto_const_nhds (hp.congr fun k => (repr k).symm)

end Liu
