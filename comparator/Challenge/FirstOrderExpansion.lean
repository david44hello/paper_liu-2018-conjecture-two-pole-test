module

public import Challenge.BlendExpansion
public import Challenge.ClusterGeometry
public import Challenge.SmallRemainder

@[expose] public section

/- Frozen input: Liu/FirstOrderExpansion.lean -/
noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped ComplexConjugate Topology
namespace Liu

def firstOrderQ (ι : ℂ) : ℂ := ((k₀-‖ι‖^2:ℝ):ℂ)-Complex.I*(ι.re:ℂ)

def firstOrderIntegrand (p q : ℂ) (z : ℂ) : ℂ :=
  let A := pole 1 p
  let B := pole 1 q
  A z*conj (B z-A z)*firstOrderQ (((A z).arg:ℂ)-optimalWitness A z)

end Liu
end
