import Challenge.TrigammaSeries
import Challenge.Mass
import Mathlib.Analysis.PSeries

/- Frozen input: Liu/CapWeights.lean -/
noncomputable section
open Real Set Filter Finset
open scoped Topology
namespace Liu

def capCoeff (τ : ℝ) (n : ℕ) := poch τ n/(n.factorial:ℝ)

def capSigma (α : ℝ) := ∑' n : ℕ, (capCoeff (2-α) n)^2 * (trigamma (n+2)/((n:ℝ)+1))

def capNorm (α : ℝ) := Gamma (2*α-2)/(Gamma α)^2

def capExpression (α : ℝ) := α^2/4*(2*trigamma α-capSigma α/capNorm α)

end Liu
end
