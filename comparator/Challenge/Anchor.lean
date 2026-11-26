import Challenge.Gluing
import Challenge.Mass

/- Frozen input: Liu/Anchor.lean -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Liu

def deepCluster : Prop := ∀ s γ T : ℝ, γ ∈ Icc 0 (Real.pi/2) → 4 ≤ T →
  (singleConstant-k₀) - 4.05/(T*(T-1)) ≤ margin s γ T

end Liu
end
