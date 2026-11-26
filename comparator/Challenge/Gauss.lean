import Challenge.Pick
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/- Frozen input: Liu/Gauss.lean -/
noncomputable section
open Set MeasureTheory Real Filter
open scoped BigOperators Topology
namespace Liu

def poch (a : ℝ) (n : ℕ) := (ascPochhammer ℝ n).eval a

end Liu
end
