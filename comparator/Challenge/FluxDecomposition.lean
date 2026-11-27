module

public import Challenge.EdgeTrace

@[expose] public section

/- Frozen input: Liu/FluxDecomposition.lean -/
noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

def edgeFluxTerms (s γ u x : ℝ) : ℝ :=
  let A := normalMass s * isolatedTrace 0 u x
  let B := (1-normalMass s) * isolatedTrace (cos γ) (sin γ+u) x
  let Z := edgeCrossTrace s γ u x
  2*A*B + 2*(A+B)*Z.re + Z.re^2 + Z.im^2

theorem edge_flux_decomposition {s γ u : ℝ} (hγ : γ ∈ Icc 0 (π/2)) (hu : 0 < u) :
    Integrable (edgeFluxTerms s γ u) ∧
    flux s γ u = (∫ x, edgeFluxTerms s γ u x)/π -
      k₀*(4*normalMass s*(1-normalMass s)*(sin γ+2*u)/(cos γ^2+(sin γ+2*u)^2)) := by sorry

end Liu
end
