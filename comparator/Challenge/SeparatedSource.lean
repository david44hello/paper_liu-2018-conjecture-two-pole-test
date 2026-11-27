module

public import Challenge.SeparatedNodes
public import Mathlib

@[expose] public section

/- Frozen input: Liu/SeparatedSource.lean -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu.PickChart

def value (P : PickChart) (w z : ℂ) : ℂ := -P.valueFactor w z/(z+Complex.I)

end Liu.PickChart
end
