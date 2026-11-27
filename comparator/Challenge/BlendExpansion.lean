module

public import Challenge.Blend
public import Challenge.OnePoleBounds

@[expose] public section

/- Frozen input: Liu/BlendExpansion.lean -/
noncomputable section
open Set Real
namespace Liu

def linearBlend (A B : ℂ) : ℂ := A*((B/A).im:ℂ)+B*((A.arg-B.arg:ℝ):ℂ)

end Liu
end
