import Challenge.CapWeights
import Challenge.SinglePoleReduction
import Challenge.SlopeFormula

/- Frozen input: Liu/LiuGammaPower.lean -/
noncomputable section
open Set Filter Real
open scoped Topology
namespace Liu

def liuNorm (p : ℝ) := Real.Gamma (2/p)*Real.Gamma (2-2/p)

theorem liuNorm_power_limit :
    Tendsto (fun d : ℝ => ((liuNorm (2+d))^(2+d)-1)/d^2) (𝓝[≠] 0) (𝓝 k₀) := by sorry

end Liu
end
