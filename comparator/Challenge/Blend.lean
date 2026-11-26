import Challenge.Witness

/- Frozen input: Liu/Blend.lean -/
noncomputable section
open Real Complex
namespace Liu

def blendedError (A B : ℂ) : ℂ :=
  A*(arg (1+B/A):ℂ) + B*(arg (1+A/B):ℂ)

end Liu
end
