module

public import Challenge.LogTailEstimate
public import Challenge.TailPhysical
public import Mathlib
public import Challenge.ReciprocalModel

@[expose] public section

/- Frozen input: Liu/PairedFlux.lean -/
noncomputable section
open Set MeasureTheory Filter Real Complex
open scoped Topology ComplexConjugate
namespace Liu

def singleDensity (p q z : ℂ) : ℂ :=
  (fieldCoefficient true*tailTerm true p q z)*(fieldCoefficient false*tailTerm false q p z) -
    (k₀:ℂ)*tailPole p z*tailPole q z

def totalDensity (P Q : Fin 3 → ℂ) (a b z : ℂ) : ℂ :=
  tailSide true P Q a b z * tailSide false Q P a b z -
    (k₀:ℂ)*(a*tailPole (P 0) z+b*tailPole (P 1) z)*(a*tailPole (Q 0) z+b*tailPole (Q 1) z)

end Liu
end
