import Challenge.FieldBound
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Challenge.BoundaryField
import Challenge.RadialEnergy
import Challenge.QuotientDomain
import Challenge.PickSums
import Mathlib.Analysis.Complex.MeanValue
import Challenge.CapWeights
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Challenge.SinglePoleReduction
import Challenge.IntegrableReproducing
import Challenge.SinglePoleDigits
import Mathlib.NumberTheory.LSeries.RiemannZeta

/- Frozen input: Liu/SinglePoleEvaluation.lean -/
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology
namespace Liu

theorem singleConstant_zeta_three : (singleConstant:ℂ)=(3/4:ℂ)*riemannZeta 3 := by sorry

theorem cap_quotient_exact {α : ℝ} (ha : 1<α) (hb : α<2) :
    quotient (capPower α)=capExpression α := by sorry

theorem cap_quotient_expansion :
    (∃ C ≥ 0, ∀ᶠ t in 𝓝[>] (0:ℝ),
      |quotient (capPower (1+t))-k₀-(π^2/6-3/2*(∑' n : ℕ, 1/(n:ℝ)^3))*t|≤C*t^2) ∧
    -0.1581513<π^2/6-3/2*(∑' n : ℕ, 1/(n:ℝ)^3) ∧
      π^2/6-3/2*(∑' n : ℕ, 1/(n:ℝ)^3)< -0.1581512 := by sorry

theorem singlePole_deficit_and_margin {a : ℝ} {w : ℂ} (ha : 0<a) (hw : w.im<0) :
    deficit (pole a w)=singleConstant*a^2 ∧
      deficit (pole a w)/a^2-k₀=singleConstant-k₀ ∧
      0.0790756<deficit (pole a w)/a^2-k₀ ∧ deficit (pole a w)/a^2-k₀<0.0790757 := by sorry

end Liu
end
