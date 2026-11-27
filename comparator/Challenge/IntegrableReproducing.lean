module

public import Challenge.Reproducing

@[expose] public section

/- Frozen input: Liu/IntegrableReproducing.lean -/
noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate
namespace Liu

def uniquenessProbe (m : ℕ) (w : ℂ) := (w-Complex.I)^m/(w+Complex.I)^(m+3)

end Liu
end
