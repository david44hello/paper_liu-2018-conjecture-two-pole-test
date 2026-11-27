module

public import Challenge.ClusterGeometry
public import Challenge.Anchor
public import Challenge.EdgeTrace

@[expose] public section

/- Frozen input: Liu/MergedPoles.lean -/
noncomputable section
open Set Real Filter MeasureTheory Metric
open scoped Topology
namespace Liu

theorem Pair.mergedPole_lower (p : Pair) (hd : p.separation≤ -p.massCentre.im/4) :
    singleConstant*p.mass^2-15*p.a₁*p.a₂*p.separation^2/(-p.massCentre.im)^2≤deficit p.value := by sorry

theorem Pair.mergedPole_deficit (p : Pair) (hd : p.separation≤ -p.massCentre.im/4) :
    let u := -p.massCentre.im
    singleConstant*p.mass^2-16.2*p.a₁*p.a₂*p.separation^2/(u*(u-p.separation))≤deficit p.value := by sorry

end Liu
end
