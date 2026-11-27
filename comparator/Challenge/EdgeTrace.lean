module

public import Challenge.SingleFlux
public import Challenge.CrossClaim
public import Challenge.FinitePart
public import Challenge.Pick
public import Challenge.PickSums
public import Challenge.Projection

@[expose] public section

/- Frozen input: Liu/EdgeTrace.lean -/
noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

def edgeCrossTrace (s γ u x : ℝ) : ℂ :=
  ∫ z, ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*crossSource (normalMass s) (direction γ) (z+(u:ℂ)*Complex.I) ∂upperArea

theorem edge_field_decomposition {s γ u : ℝ} (hγ : γ ∈ Icc 0 (π/2)) (hu : 0 < u) (x : ℝ) :
    let a := normalMass s
    let b := 1-a
    field (normalSum s γ u) x =
      -(((a*isolatedTrace 0 u x + b*isolatedTrace (cos γ) (sin γ+u) x:ℝ):ℂ) + edgeCrossTrace s γ u x) := by sorry

end Liu
end
