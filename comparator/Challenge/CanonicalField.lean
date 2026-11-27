module

public import Challenge.CauchyTransform
public import Challenge.FieldBound
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Challenge.BoundaryField
public import Challenge.RadialEnergy
public import Challenge.QuotientDomain
public import Challenge.PickSums
public import Mathlib.Analysis.Complex.MeanValue
public import Challenge.PoissonLine
public import Challenge.LogSource
public import Challenge.Witness
public import Mathlib.Analysis.Complex.Conformal

@[expose] public section

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
