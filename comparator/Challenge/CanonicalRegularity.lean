module

public import Challenge.CanonicalField
public import Challenge.FinitePart
public import Challenge.Pick
public import Challenge.PickSums
public import Challenge.Projection
public import Challenge.Reproducing
public import Challenge.LogSource

@[expose] public section

/- Frozen input: Liu/CanonicalRegularity.lean -/
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate
namespace Liu

theorem canonicalField_dbar {f : ℂ → ℂ} (hf : QuadraticDecay f)
    {z : ℂ} (hz : z∈upper) (hd : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (canonicalField f) z ∧ dbar (canonicalField f) z=f z := by sorry

end Liu
end
