import Challenge.CanonicalField
import Challenge.FinitePart
import Challenge.Pick
import Challenge.PickSums
import Challenge.Projection
import Challenge.Reproducing
import Challenge.LogSource

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
