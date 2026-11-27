module

public import Challenge.OnePoleBounds
public import Challenge.Blend

@[expose] public section

/- Frozen input: Liu/ClusterGeometry.lean -/
noncomputable section
open Set Real
namespace Liu

def Pair.massFraction (p : Pair) := p.a₁/p.mass

def Pair.massCentre (p : Pair) : ℂ :=
  p.w₂ + (p.massFraction:ℂ)*(p.w₁-p.w₂)

def Pair.separation (p : Pair) := ‖p.w₁-p.w₂‖

end Liu
end
