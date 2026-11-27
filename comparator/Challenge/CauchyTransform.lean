module

public import Challenge.FieldBound
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

@[expose] public section

/- Frozen input: Liu/CauchyTransform.lean -/
noncomputable section
open Set MeasureTheory Real Filter
open scoped ComplexConjugate Topology
namespace Liu

def cauchyTransform (f : ℂ → ℂ) (x : ℂ) : ℂ :=
  ∫ w, f w/(x-w) ∂upperArea

structure QuadraticDecay (f : ℂ → ℂ) : Prop where
  measurable : Measurable f
  bound : ∃ K ≥ 0, ∀ w ∈ upper, ‖f w‖ ≤ K/(1+‖w‖)^2

end Liu
end
