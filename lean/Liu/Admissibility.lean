import Liu.ResidualBound

noncomputable section
open Set MeasureTheory
namespace Liu

/-- Lemma 3.2. For each finite nonempty Pick sum and every allowed exponent
window, the domination is for a representative of the actual projected residual. -/
theorem PickSum.admissible_critical {n : ℕ} (p : PickSum n) {ε η : ℝ}
    (he : 0 < ε) (he1 : ε < 1) (hη : 0 < η) (hη' : η < 2*ε/(1+ε)) :
    let F := p.power (1+ε)
    DifferentiableOn ℂ F upper ∧ (∀ z ∈ upper, F z ≠ 0) ∧ MemLp F 2 upperArea ∧
    MemLp (logInput F) 2 upperArea ∧ 0 < ‖asL2 F‖ ∧
    (∀ v : ℝ, |v-2| ≤ η → Integrable (fun z => ‖F z‖^v * (1+|Real.log ‖F z‖|)^5) upperArea) ∧
      ∃ G : ℂ → ℂ, ∃ hG : MemLp G 2 upperArea,
        hG.toLp G = asL2 (logInput F)-project (asL2 (logInput F)) ∧
        ∃ C > 0, ∀ z ∈ upper, ‖G z‖ ≤ C*‖F z‖*(1+|Real.log ‖F z‖|) := by
  obtain ⟨a,b,c,d,e,f⟩ := p.critical_window he hη'
  exact ⟨a,b,c,d,e,f,p.projected_domination (by linarith : 1 < 1+ε) (by linarith)⟩

end Liu
