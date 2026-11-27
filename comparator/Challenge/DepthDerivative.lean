module

public import Challenge.SmallFirstOrder
public import Challenge.DepthTraceContinuity
public import Challenge.Reflection
public import Challenge.QuotientDomain
public import Challenge.PickSums
public import Challenge.RadialEnergy
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Challenge.Pick
public import Challenge.CauchyTransform
public import Challenge.DepthFluxContinuity
public import Challenge.SmallMassDeficit

@[expose] public section

/- Frozen input: Liu/DepthDerivative.lean -/
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

theorem PickSum.flux_law_at {n : ℕ} (p : PickSum n) {a : ℝ} (ha : ∀ i, (p.location i).im<a) :
    HasDerivAt (fun t : ℝ => deficit (depthTranslate p.value t))
      (boundaryFlux (depthTranslate p.value a)) a := by sorry

theorem PickSum.flux_continuousAt_valid_depth {n : ℕ} (p : PickSum n) {a : ℝ}
    (ha : ∀ i, (p.location i).im<a) :
    ContinuousAt (fun t => boundaryFlux (depthTranslate p.value t)) a := by sorry

theorem PickSum.finite_depth_flux_law {n : ℕ} (p : PickSum n) {u v : ℝ} (hu : ∀ i, (p.location i).im<u)
    (huv : u≤v) :
    let F := fun t => boundaryFlux (depthTranslate p.value t)
    IntervalIntegrable F volume u v ∧
    deficit (depthTranslate p.value u) = deficit (depthTranslate p.value v) - ∫ t in u..v,F t := by sorry

theorem depth_flux_hasDerivAt (s γ : ℝ) (hγ : γ∈Icc 0 (π/2)) {u : ℝ} (hu : 0<u) :
    HasDerivAt (margin s γ) (flux s γ u) u := by sorry

theorem depth_flux_contDiff (s γ : ℝ) (hγ : γ∈Icc 0 (π/2)) :
    ContDiffOn ℝ 1 (margin s γ) (Ioi 0) := by sorry

theorem depth_flux_identity : Certificate.fluxIdentity := by sorry

theorem depth_anchor {s γ u L : ℝ} (hγ : γ∈Icc 0 (π/2)) (hu : 0<u)
    (conv : Tendsto (fun T => ∫ t in u..T,flux s γ t) atTop (𝓝 L)) :
    (singleConstant-k₀)-L ≤ margin s γ u := by sorry

end Liu
end
