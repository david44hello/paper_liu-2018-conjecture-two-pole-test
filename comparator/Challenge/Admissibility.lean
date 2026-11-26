import Challenge.ProjectionKernel
import Challenge.FinitePart
import Challenge.Pick
import Challenge.PickSums
import Challenge.Projection
import Challenge.Reproducing
import Challenge.LogSource

/- Frozen input: Liu/Admissibility.lean -/
noncomputable section
open Set MeasureTheory
namespace Liu

theorem PickSum.admissible_critical {n : ℕ} (p : PickSum n) {ε η : ℝ}
    (he : 0 < ε) (he1 : ε < 1) (hη : 0 < η) (hη' : η < 2*ε/(1+ε)) :
    let F := p.power (1+ε)
    DifferentiableOn ℂ F upper ∧ (∀ z ∈ upper, F z ≠ 0) ∧ MemLp F 2 upperArea ∧
    MemLp (logInput F) 2 upperArea ∧ 0 < ‖asL2 F‖ ∧
    (∀ v : ℝ, |v-2| ≤ η → Integrable (fun z => ‖F z‖^v * (1+|Real.log ‖F z‖|)^5) upperArea) ∧
      ∃ G : ℂ → ℂ, ∃ hG : MemLp G 2 upperArea,
        hG.toLp G = asL2 (logInput F)-project (asL2 (logInput F)) ∧
        ∃ C > 0, ∀ z ∈ upper, ‖G z‖ ≤ C*‖F z‖*(1+|Real.log ‖F z‖|) := by sorry

end Liu
end
