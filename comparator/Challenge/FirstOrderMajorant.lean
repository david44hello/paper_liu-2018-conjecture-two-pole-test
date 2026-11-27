module

public import Challenge.FirstOrderExpansion
public import Challenge.PoissonLine

@[expose] public section

/- Frozen input: Liu/FirstOrderMajorant.lean -/
noncomputable section
open Set Real MeasureTheory Metric
open scoped ComplexConjugate
namespace Liu

theorem firstOrderIntegral_bound {q : ℂ} (hq : q.im<0) :
    Integrable (firstOrderIntegrand (-Complex.I) q) upperArea ∧
    |(∫ z, firstOrderIntegrand (-Complex.I) q z ∂upperArea).re|≤79 := by sorry

end Liu
end
