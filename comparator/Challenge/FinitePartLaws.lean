module

public import Challenge.RadialField
public import Challenge.Reflection
public import Challenge.QuotientDomain
public import Challenge.PickSums
public import Challenge.RadialEnergy
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section

/- Frozen input: Liu/FinitePartLaws.lean -/
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

theorem PickSum.finite_part_laws {n : ℕ} (p : PickSum n) :
    finitePartExists p.value ∧
    (∀ x : ℝ, finitePartExists (fun z => p.value (z-(x:ℂ))) ∧
      deficit (fun z => p.value (z-(x:ℂ)))=deficit p.value) ∧
    (∀ scale : ℝ, 0<scale → deficit (fun z => ((scale⁻¹:ℝ):ℂ)*p.value (z/(scale:ℂ))) = deficit p.value) ∧
    deficit (reflectFunction p.value) = deficit p.value ∧
    (∀ c : ℝ, deficit (fun z => (c:ℂ)*p.value z)=c^2*deficit p.value) := by sorry

end Liu
end
