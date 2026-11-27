module

public import Liu.EdgeContinuity
public import Liu.EdgeImagTrace

@[expose] public section

noncomputable section
open Set Real MeasureTheory
namespace Liu

/-- Lemma E.3. Line norms use dx/π. The real trace has a pointwise bound
and both components at u=0 are the paper's Poisson convolutions. -/
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
      (∀ u : ℝ, 0<u → u≤1/4 → ∀ x : ℝ, |c u x-c 0 x|≤4*C₂*u*(1+log (1/u)))) := by
  constructor
  · intro hc u hu _
    obtain ⟨hi,h₁,hp⟩ := edge_real_trace_separated (s:=s) hg hc hu.le
    obtain ⟨hL,hq⟩ := edge_imag_trace_separated (s:=s) hg hc hu.le
    have hμ : 0 < min (normalMass s) (1-normalMass s) := lt_min (Certificate.normalMass_pos _)
      (by rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _)
    exact ⟨hi,h₁,hp,hL,(sqrt_le_sqrt hq).trans_eq (sqrt_sq (by positivity))⟩
  · intro hσ
    refine ⟨?_,edge_real_trace_moduli (s:=s) hg hσ⟩
    intro u hu _
    obtain ⟨hi,h₁,hp⟩ := edge_real_trace_fixed (s:=s) hg hσ hu
    obtain ⟨hL,hq⟩ := edge_imag_trace_fixed (s:=s) hg hσ hu
    exact ⟨hi,h₁,hp,hL,(sqrt_le_sqrt hq).trans_eq (sqrt_sq (by positivity))⟩

end Liu
