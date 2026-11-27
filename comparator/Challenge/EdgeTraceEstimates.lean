module

public import Challenge.CrossClaim
public import Challenge.EdgeConvolution
public import Challenge.RadialEnergy
public import Challenge.Pick
public import Challenge.PickSums
public import Challenge.Projection
public import Challenge.EdgeRealTrace

@[expose] public section

/- Frozen input: Liu/EdgeTraceEstimates.lean -/
noncomputable section
open Set Real MeasureTheory
namespace Liu

theorem edge_trace_estimates (s γ : ℝ) (hg : γ∈Icc 0 (π/2)) :
    let a := normalMass s
    let C₁ := 2^15/min a (1-a)
    let C₂ := 8/(a*sin γ^4)
    let c := edgeRealTrace s γ
    let q := edgeImagTrace s γ
    (1/2≤cos γ → ∀ u : ℝ, 0<u → u≤1/4 →
      Integrable (c u) ∧ (∫ x, |c u x|)/π≤C₁ ∧ (∀ x, |c u x|≤5*C₁) ∧
      MemLp (q u) 2 volume ∧ sqrt ((∫ x, q u x^2)/π)≤C₁) ∧
    (0<sin γ →
      (∀ u : ℝ, 0≤u → u≤1/4 → Integrable (c u) ∧ (∫ x, |c u x|)/π≤C₂ ∧
        (∀ x, |c u x|≤3*C₂) ∧ MemLp (q u) 2 volume ∧ sqrt ((∫ x, q u x^2)/π)≤16/sin γ^3) ∧
      (∀ x : ℝ, 0 < |x| → |x|≤1/4 → |c 0 x-c 0 0|≤4*C₂*|x| *(1+log (1/|x|))) ∧
      (∀ u : ℝ, 0<u → u≤1/4 → ∀ x : ℝ, |c u x-c 0 x|≤4*C₂*u*(1+log (1/u)))) := by sorry

end Liu
end
