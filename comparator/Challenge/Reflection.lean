import Challenge.FinitePart
import Challenge.Pick
import Challenge.PickSums
import Challenge.Projection

/- Frozen input: Liu/Reflection.lean -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu

def verticalReflection : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)

def reflectFunction (S : ℂ → ℂ) : ℂ → ℂ := verticalReflection ∘ S ∘ verticalReflection

end Liu
end
