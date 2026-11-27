module

public import Challenge.FarFieldClaim
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

/- Frozen input: Liu/Orthogonality.lean -/
noncomputable section
open Set MeasureTheory Real Filter
open scoped ComplexConjugate Topology
namespace Liu

theorem PickSum.field_orthogonality {n : ℕ} (p : PickSum n) {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g upper) (hc : ContinuousOn g {z : ℂ | 0≤z.im})
    {T K : ℝ} (hK : 0≤K)
    (hg : ∀ z : ℂ, 0≤z.im → T≤‖z‖ → ‖g z‖ ≤ K*(1+log ‖z‖)/‖z‖^2) :
    Integrable (fun z => field p.value z*conj (g z)) upperArea ∧
      (∫ z, field p.value z*conj (g z) ∂upperArea)=0 := by sorry

end Liu
end
