import Challenge.SmallFirstOrder
import Challenge.BlendExpansion
import Challenge.ClusterGeometry
import Challenge.MergedPoles

/- Frozen input: Liu/SmallMassDeficit.lean -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Liu

theorem Pair.small_mass_margin (p : Pair) (hs : min p.a₁ p.a₂≤ max p.a₁ p.a₂/4096) :
    (38/1000:ℝ)*(max p.a₁ p.a₂)^2<deficit p.value-k₀*p.mass^2 ∧
    0<deficit p.value/p.mass^2-k₀ := by sorry

end Liu
end
