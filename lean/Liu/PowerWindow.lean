import Liu.QuotientDomain

noncomputable section
open MeasureTheory Set
namespace Liu

theorem PickSum.power_holomorphic {n : ℕ} (p : PickSum n) (t : ℝ) :
    DifferentiableOn ℂ (p.power t) upper :=
  p.holomorphic.cpow_const (fun _ hz => Complex.mem_slitPlane_iff.mpr
    (Or.inr (p.value_im_pos (le_of_lt hz)).ne'))

theorem PickSum.power_nonzero {n : ℕ} (p : PickSum n) (t : ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    p.power t z ≠ 0 := by
  have h : p.value z ≠ 0 := fun he => by
    have hi := p.value_im_pos hz
    simp [he] at hi
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl h)

theorem PickSum.critical_window {n : ℕ} (p : PickSum n) {ε η : ℝ}
    (he : 0<ε) (hη : η < 2*ε/(1+ε)) :
    let F := p.power (1+ε)
    DifferentiableOn ℂ F upper ∧ (∀ z ∈ upper, F z ≠ 0) ∧
      MemLp F 2 upperArea ∧ MemLp (logInput F) 2 upperArea ∧ 0 < ‖asL2 F‖ ∧
      ∀ v : ℝ, |v-2| ≤ η →
        Integrable (fun z => ‖F z‖^v*(1+|Real.log ‖F z‖|)^5) upperArea := by
  have ht : 1 < 1+ε := by linarith
  exact ⟨p.power_holomorphic _, fun _ hz => p.power_nonzero _ (le_of_lt hz),
    p.power_memLp_two ht,p.log_power_memLp_two ht,p.powerL2_norm_pos ht,
    fun _ hv => p.integrability_window he hη hv⟩

end Liu
