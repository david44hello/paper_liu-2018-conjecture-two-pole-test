module

public import Challenge.CitedInterpolation
public import Challenge.SlopeFormula
public import Challenge.ProjectionKernel

@[expose] public section

/- Frozen input: Liu/TrialIntegral.lean -/
noncomputable section
open Set Real Complex Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace Liu

structure TrialWindow (F G : ℂ → ℂ) (η C : ℝ) : Prop where
  radius : 0<η
  small : η≤1
  constant_nonneg : 0≤C
  input : MemLp F 2 upperArea
  direction : MemLp G 2 upperArea
  nonzero : ∀ᵐ z ∂upperArea, F z≠0
  ratio : ∀ᵐ z ∂upperArea, ‖G z/F z‖≤C*(1+|Real.log ‖F z‖|)
  lower : Integrable (fun z => ‖F z‖^(2-η)*(1+|Real.log ‖F z‖|)^5) upperArea
  higher : Integrable (fun z => ‖F z‖^(2+η)*(1+|Real.log ‖F z‖|)^5) upperArea

end Liu
end
