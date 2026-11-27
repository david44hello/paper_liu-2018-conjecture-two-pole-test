module

public import Challenge.LogTailEstimate
public import Challenge.TailPhysical
public import Mathlib
public import Challenge.ReciprocalModel

@[expose] public section

/- Frozen input: Liu/CentredMovement.lean -/
noncomputable section
open Set Complex
namespace Liu

def massCentre (a b : ℂ) (P : Fin 3 → ℂ) := a*P 0+b*P 1

def movingNode (a b : ℂ) (P : Fin 3 → ℂ) (j : Fin 3) (t : ℂ) : ℂ :=
  massCentre a b P+t*(P j-massCentre a b P)

end Liu
end
