import Challenge.WeakBergman
import Challenge.WitnessClaim
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Complex.Convex

/- Frozen input: Liu/DirichletDerivatives.lean -/
noncomputable section
open Set Filter MeasureTheory Real Complex
open scoped Topology ContDiff InnerProductSpace ComplexConjugate
namespace Liu

def closedUpper := {z : ℂ | 0≤z.im}

end Liu
end
