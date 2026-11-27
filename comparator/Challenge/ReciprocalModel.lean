module

public import Mathlib
public import Challenge.CertificateConclusion
public import Challenge.FinitePart
public import Challenge.Pick
public import Challenge.PickSums
public import Challenge.Projection

@[expose] public section

/- Frozen input: Liu/ReciprocalModel.lean -/
noncomputable section
open Set Real MeasureTheory Metric
open scoped ComplexConjugate Topology
namespace Liu

def unitDepthSum (s γ v : ℝ) (z : ℂ) : ℂ :=
  pole (normalMass s) (-Complex.I) z +
  pole (1-normalMass s) (-Complex.I+(v:ℂ)*direction γ) z

end Liu
end
