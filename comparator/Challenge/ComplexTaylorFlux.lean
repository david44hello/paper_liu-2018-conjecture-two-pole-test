module

public import Challenge.CentredDensity

@[expose] public section

/- Frozen input: Liu/ComplexTaylorFlux.lean -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology ComplexConjugate
namespace Liu

def pairedBoundaryFlux (P Q : Fin 3 → ℂ) (a b : ℂ) : ℂ :=
  (∫ x : ℝ, totalDensity P Q a b x)/(Real.pi:ℂ)

theorem Pair.pairedBoundaryFlux_actual (P : Pair) (hm : P.a₁+P.a₂=1) :
    pairedBoundaryFlux P.tailNodes (fun i => conj (P.tailNodes i)) P.a₁ P.a₂ = (boundaryFlux P.toPick.value:ℂ) := by sorry

theorem centred_taylor_flux (a b : ℂ) (hab : a+b=1) (P Q : Fin 3 → ℂ)
    (hP : P 2=a*P 1+b*P 0) (hQ : Q 2=a*Q 1+b*Q 0)
    (hsep : ∀ r ∈ Icc (0:ℝ) 1, ∀ j, (movingNode a b P j r).im<0 ∧ 0<(movingNode a b Q j r).im) :
    let H := movedSubtraction a b P Q
    let D := fun x => deriv (fun t => H t x) 0
    (∃ U : Set ℂ, IsOpen U ∧ (∀ r∈Icc (0:ℝ) 1, (r:ℂ)∈U) ∧
      ∀ x, AnalyticOnNhd ℂ (fun t => H t x) U) ∧
    (∀ x, H 0 x=2*a*b*singleDensity (massCentre a b P) (massCentre a b Q) x) ∧
    Integrable (H 0) ∧ Integrable D ∧ (∫ x, H 0 x)=0 ∧ (∫ x, D x)=0 ∧
    (Real.pi:ℂ)*pairedBoundaryFlux P Q a b = ∫ x, H 1 x-H 0 x-D x := by sorry

end Liu
end
