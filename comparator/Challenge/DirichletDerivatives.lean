module

public import Challenge.WeakBergman
public import Challenge.WitnessClaim
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Complex.Convex

@[expose] public section

/- Frozen input: Liu/DirichletDerivatives.lean -/
noncomputable section
open Set Filter MeasureTheory Real Complex
open scoped Topology ContDiff InnerProductSpace ComplexConjugate
namespace Liu

def closedUpper := {z : ℂ | 0≤z.im}

end Liu
end
