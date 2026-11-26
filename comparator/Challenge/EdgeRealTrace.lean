import Challenge.CrossClaim
import Challenge.EdgeConvolution
import Challenge.RadialEnergy
import Challenge.Pick
import Challenge.PickSums
import Challenge.Projection

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
