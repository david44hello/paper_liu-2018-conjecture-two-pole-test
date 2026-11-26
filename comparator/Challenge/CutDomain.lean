import Mathlib
import Challenge.CutSeparation

/- Frozen input: Liu/CutDomain.lean -/
noncomputable section
open Set Filter Real Complex
open scoped Topology
namespace Liu

def cutHeights (P Q : Fin 3 → ℂ) (x : ℝ) : Set ℝ :=
  {y | (∀ i, x=(P i).re → (P i).im < y) ∧ (∀ j, x=(Q j).re → y < (Q j).im)}

def offCuts (P Q : Fin 3 → ℂ) : Set ℂ := {z | z.im∈cutHeights P Q z.re}

end Liu
end
