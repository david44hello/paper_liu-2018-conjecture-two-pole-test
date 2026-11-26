import Challenge.Blend
import Challenge.OnePoleBounds

/- Frozen input: Liu/BlendExpansion.lean -/
noncomputable section
open Set Real
namespace Liu

def linearBlend (A B : ℂ) : ℂ := A*((B/A).im:ℂ)+B*((A.arg-B.arg:ℝ):ℂ)

end Liu
end
