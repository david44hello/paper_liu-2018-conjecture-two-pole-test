module

public import Challenge.RadialField
public import Challenge.AngularPotential
public import Challenge.FinitePartLaws

@[expose] public section

/- Frozen input: Liu/FarFieldClaim.lean -/
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology
namespace Liu

theorem PickSum.far_field {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → 1<‖z‖ →
      ‖potential p.value z-Complex.I*((p.mass/2*z.arg*(π-z.arg):ℝ):ℂ)‖ ≤ C*(1+log ‖z‖)/‖z‖ ∧
      ‖fderiv ℝ (fun w => potential p.value w-angularPotential p.mass w) z‖ ≤ C*(1+log ‖z‖)/‖z‖^2 ∧
      ‖field p.value z-fieldFarModel p.mass z‖ ≤ C*(1+log ‖z‖)/‖z‖^2 := by sorry

end Liu
end
