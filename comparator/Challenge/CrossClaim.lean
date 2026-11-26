import Challenge.CrossSource
import Challenge.Prefix

/- Frozen input: Liu/CrossClaim.lean -/
noncomputable section
open scoped ComplexConjugate
namespace Liu

theorem cross_source_claim (s γ : ℝ) (hγ : γ ∈ Set.Icc 0 (Real.pi/2))
    {z : ℂ} (hz : 0 < z.im) :
    let a := normalMass s
    let q := direction γ
    let Y := z.re*Real.sin γ + z.im*Real.cos γ
    let D := ‖z‖^2*‖z-q‖^2
    crossSource a q z = (2*Complex.I*(a:ℂ)*(1-a)*conj q*(Y:ℂ)) /
      ((D:ℂ)*(conj z-(a:ℂ)*conj q)) ∧
    (crossSource a q z).re = -2*a*(1-a)*Y^2/(D*‖z-(a:ℂ)*q‖^2) ∧
    (crossSource a q z).re ≤ 0 ∧
    ‖crossSource a q z‖ = 2*a*(1-a)*|Y| / (D*‖z-(a:ℂ)*q‖) ∧
    |Y| ≤ min ‖z‖ (min ‖z-q‖ ‖z-(a:ℂ)*q‖) := by sorry

end Liu
end
