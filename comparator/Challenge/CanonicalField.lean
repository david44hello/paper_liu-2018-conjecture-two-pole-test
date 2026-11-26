import Challenge.CauchyTransform
import Challenge.FieldBound
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Challenge.BoundaryField
import Challenge.RadialEnergy
import Challenge.QuotientDomain
import Challenge.PickSums
import Mathlib.Analysis.Complex.MeanValue
import Challenge.PoissonLine
import Challenge.LogSource
import Challenge.Witness
import Mathlib.Analysis.Complex.Conformal

/- Frozen input: Liu/CanonicalField.lean -/
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology ComplexConjugate
namespace Liu

def canonicalField (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  cauchyTransform f z-conj (cauchyTransform (fun w => conj (f w)) (conj z))

theorem canonicalField_continuous {f : ℂ → ℂ} (hf : QuadraticDecay f) : Continuous (canonicalField f) := by sorry

theorem canonicalField_holomorphic_difference {f h : ℂ → ℂ} (hf : QuadraticDecay f)
    {z : ℂ} (hz : z∈upper) (hdf : DifferentiableAt ℝ f z) (hdh : DifferentiableAt ℝ h z) (hb : dbar h z=f z) :
    DifferentiableAt ℂ (fun x => h x-canonicalField f x) z := by sorry

end Liu
end
