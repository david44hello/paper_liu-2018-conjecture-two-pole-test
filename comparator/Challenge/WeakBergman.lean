import Challenge.QuotientDomain
import Challenge.PickSums
import Challenge.RadialEnergy
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Challenge.WeakPrimitive
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/- Frozen input: Liu/WeakBergman.lean -/
noncomputable section
open Set Filter MeasureTheory Real Metric
open scoped Topology ENNReal
namespace Liu

theorem weak_holomorphic_mem_analytic {h : ℂ → ℂ} (hh : MemLp h 2 upperArea) (hw : WeakDbar h 0) :
    hh.toLp h∈analyticVectors := by sorry

theorem SupercriticalSource.field_and_weak_projection {f : ℂ → ℂ} {t : ℝ} (hf : SupercriticalSource f t)
    (df : DifferentiableOn ℝ f upper) :
    ContinuousOn (canonicalField f) {z : ℂ | 0≤z.im} ∧
    (∃ C≥0, ∀ z : ℂ, 0≤z.im → ‖canonicalField f z‖≤C/(1+‖z‖)^(1+t)) ∧
    MemLp (canonicalField f) 2 upperArea ∧
    ∀ h : ℂ → ℂ, MemLp h 2 upperArea → WeakDbar h f → asL2 h-project (asL2 h)=asL2 (canonicalField f) := by sorry

end Liu
end
