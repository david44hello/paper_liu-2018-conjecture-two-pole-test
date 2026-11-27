module

public import Challenge.SupercriticalEnergy
public import Challenge.ProjectionKernel
public import Challenge.QuotientDomain
public import Challenge.PickSums
public import Challenge.RadialEnergy

@[expose] public section

/- Frozen input: Liu/WeakPrimitive.lean -/
noncomputable section
open Set Filter MeasureTheory Complex Real
open scoped Topology ContDiff
namespace Liu

def WeakDbar (h f : ℂ → ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ upper →
    (∫ z, h z*dbar φ z ∂upperArea) = -(∫ z, f z*φ z ∂upperArea)

end Liu
end
