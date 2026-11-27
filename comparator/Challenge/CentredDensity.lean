module

public import Challenge.SinglePartnerFlux
public import Challenge.CentredMovement

@[expose] public section

/- Frozen input: Liu/CentredDensity.lean -/
noncomputable section
open Set MeasureTheory Filter Real Complex
open scoped Topology
namespace Liu

def movedSubtraction (a b : ℂ) (P Q : Fin 3 → ℂ) (t : ℂ) (x : ℝ) : ℂ :=
  subtractedTail (fun i => movingNode a b P i t) (fun i => movingNode a b Q i t) a b x

end Liu
end
