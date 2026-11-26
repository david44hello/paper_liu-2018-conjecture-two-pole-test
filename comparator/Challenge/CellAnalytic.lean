import Challenge.TopCollision
import Challenge.ChebyshevEllipse
import Challenge.CellPartners

/- Frozen input: Liu/CellAnalytic.lean -/
noncomputable section
open Set Real Filter
open scoped Topology
namespace Liu

theorem interpolation_cell_analytic (L : CellLine) (u ρ : ℝ)
    (axis : L.y₁=0 ∨ L.s₁=0 ∧ L.g₁=0) :
    ((∀ w∈bernsteinEllipse ρ, L.partnerTests (L.depth u) (fun _ => 1) w) →
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (bernsteinEllipse ρ) ∧
        ∀ t : ℝ, (t:ℂ)∈bernsteinEllipse ρ → F t =
          ((u*exp (L.y₀+L.y₁*t-1)*flux (L.s₀+L.s₁*t) (L.realAngle t)
            (u*exp (L.y₀+L.y₁*t-1)):ℝ):ℂ)) ∧
    ((∀ w∈bernsteinEllipse ρ, L.partnerTests (fun _ => 1) L.reciprocal w) →
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (bernsteinEllipse ρ) ∧
        ∀ t : ℝ, (t:ℂ)∈bernsteinEllipse ρ → F t=(topCellFlux L t:ℂ)) := by sorry

end Liu
end
