module

public import Challenge.QuotientDomain
public import Challenge.PickSums
public import Challenge.RadialEnergy

@[expose] public section

/- Frozen input: Liu/Witness.lean -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu

def isWitness (W : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ W upper ∧ ContinuousOn W {z : ℂ | 0 ≤ z.im} ∧
    ∃ C > 0, ∃ R > 0, ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ →
      ‖W z - (Real.pi/2:ℝ)‖ ≤ C*(1+Real.log ‖z‖)/‖z‖

def optimalWitness (S : ℂ → ℂ) (z : ℂ) : ℂ :=
  (S z*(Complex.arg (S z):ℂ)-field S z)/S z

def witnessDifference (S W : ℂ → ℂ) (z : ℂ) := S z * (W z - optimalWitness S z)

def truncatedWitness (S W : ℂ → ℂ) (R : ℝ) : ℝ :=
  ∫ z in halfDisc R, k₀*‖S z‖^2 - ‖S z‖^2*‖(Complex.arg (S z):ℂ)-W z‖^2 ∂area

end Liu
end
