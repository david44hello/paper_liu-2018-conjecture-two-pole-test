module

public import Challenge.CrossClaim
public import Challenge.EdgeConvolution
public import Challenge.RadialEnergy
public import Challenge.Pick
public import Challenge.PickSums
public import Challenge.Projection

@[expose] public section

/- Frozen input: Liu/EdgeRealTrace.lean -/
noncomputable section
open Set Real MeasureTheory
namespace Liu

def edgeRealTrace (s γ u x : ℝ) : ℝ :=
  depthPoissonReal u x (fun z => (crossSource (normalMass s) (direction γ) z).re)

def edgeImagTrace (s γ u x : ℝ) : ℝ :=
  depthPoissonReal u x (fun z => (crossSource (normalMass s) (direction γ) z).im)

end Liu
end
