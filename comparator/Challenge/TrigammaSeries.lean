module

public import Challenge.Gauss
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

@[expose] public section

/- Frozen input: Liu/TrigammaSeries.lean -/
noncomputable section
open Set Real Filter Finset
open scoped Topology
namespace Liu

def psi (x : ℝ) := deriv (Real.log ∘ Real.Gamma) x

def trigamma (x : ℝ) := deriv psi x

end Liu
end
