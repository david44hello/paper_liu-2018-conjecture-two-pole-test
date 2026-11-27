module

public import Liu.LocalParameterIntegral
public import Liu.ReciprocalFlux

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Liu

/-- Holomorphic families on the real observation line that have a common
local Lᵖ majorant in the parameter. -/
structure DominatedFamily (p : ℝ≥0∞) (U : Set ℂ) (F : ℂ → ℝ → ℂ) : Prop where
  measurable : ∀ t, AEStronglyMeasurable (F t) volume
  differentiable : ∀ x, DifferentiableOn ℂ (fun t => F t x) U
  bound : ∀ c∈U, ∃ M : ℝ → ℝ, MemLp M p volume ∧ ∀ᶠ t in 𝓝 c, ∀ x, ‖F t x‖≤M x

theorem DominatedFamily.add {p U F G} (h : DominatedFamily p U F) (k : DominatedFamily p U G) :
    DominatedFamily p U (fun t x => F t x+G t x) := by
  refine ⟨fun t => (h.measurable t).add (k.measurable t),fun x => (h.differentiable x).add (k.differentiable x),?_⟩
  intro c hc
  obtain ⟨M,hi,hM⟩ := h.bound c hc
  obtain ⟨N,hj,hN⟩ := k.bound c hc
  refine ⟨fun x => M x+N x,hi.add hj,?_⟩
  filter_upwards [hM,hN] with t ht hs
  exact fun x => (norm_add_le ..).trans (add_le_add (ht x) (hs x))

theorem DominatedFamily.const_mul {p U F} (h : DominatedFamily p U F) (a : ℂ) :
    DominatedFamily p U (fun t x => a*F t x) := by
  refine ⟨fun t => (h.measurable t).const_mul _,fun x => (h.differentiable x).const_mul _,?_⟩
  intro c hc
  obtain ⟨M,hi,hM⟩ := h.bound c hc
  refine ⟨fun x => ‖a‖*M x,hi.const_smul ‖a‖,?_⟩
  filter_upwards [hM] with t ht x
  rw [norm_mul]; exact mul_le_mul_of_nonneg_left (ht x) (norm_nonneg _)

theorem DominatedFamily.sub {p U F G} (h : DominatedFamily p U F) (k : DominatedFamily p U G) :
    DominatedFamily p U (fun t x => F t x-G t x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using h.add (k.const_mul (-1))

theorem DominatedFamily.mul_two {U F G} (h : DominatedFamily 2 U F) (k : DominatedFamily 2 U G) :
    DominatedFamily 1 U (fun t x => F t x*G t x) := by
  refine ⟨fun t => (h.measurable t).mul (k.measurable t),fun x => (h.differentiable x).mul (k.differentiable x),?_⟩
  intro c hc
  obtain ⟨M,hi,hM⟩ := h.bound c hc
  obtain ⟨N,hj,hN⟩ := k.bound c hc
  refine ⟨fun x => M x*N x,memLp_one_iff_integrable.mpr (hi.integrable_mul hj),?_⟩
  filter_upwards [hM,hN] with t ht hs x
  rw [norm_mul]
  exact mul_le_mul (ht x) (hs x) (norm_nonneg _) ((norm_nonneg _).trans (ht x))

theorem DominatedFamily.integrable {U F} (h : DominatedFamily 1 U F) {t : ℂ} (ht : t∈U) :
    Integrable (F t) volume := by
  obtain ⟨M,hi,hM⟩ := h.bound t ht
  exact (memLp_one_iff_integrable.mp hi).mono' (h.measurable _) (Eventually.of_forall hM.self_of_nhds)

theorem DominatedFamily.integral_hasDeriv {U F} (h : DominatedFamily 1 U F) (ho : IsOpen U)
    {t : ℂ} (ht : t∈U) : HasDerivAt (fun w => ∫ x, F w x) (∫ x, deriv (fun w => F w x) t) t := by
  obtain ⟨M,hi,hM⟩ := h.bound t ht
  exact hasDerivAt_local_integral volume ho ht h.measurable (Eventually.of_forall h.differentiable)
    (memLp_one_iff_integrable.mp hi) (V:={w | ∀ x, ‖F w x‖≤M x}) hM
    (Eventually.of_forall (fun x _ hw => hw x))

theorem DominatedFamily.deriv_integrable {U F} (h : DominatedFamily 1 U F) (ho : IsOpen U)
    {c : ℂ} (hc : c∈U) : Integrable (fun x => deriv (fun w => F w x) c) volume := by
  obtain ⟨M,hi,hM⟩ := h.bound c hc
  let V := {w | ∀ x, ‖F w x‖≤M x}
  obtain ⟨R,hR,hB⟩ := Metric.mem_nhds_iff.mp (inter_mem (show V∈𝓝 c from hM) (ho.mem_nhds hc))
  apply (((memLp_one_iff_integrable.mp hi).const_mul 2).div_const R).mono'
  · apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] c) (f:=fun w x => slope (fun v => F v x) c w)
    · intro w; exact ((h.measurable w).sub (h.measurable c)).const_smul ((w-c)⁻¹)
    · exact Eventually.of_forall fun x => hasDerivAt_iff_tendsto_slope.mp
        ((h.differentiable x).differentiableAt (ho.mem_nhds hc)).hasDerivAt
  · filter_upwards with x
    apply Complex.norm_deriv_le_div_of_mapsTo_ball ((h.differentiable x).mono fun w hw => (hB hw).2) _ hR
    intro w hw
    rw [mem_closedBall_iff_norm]
    linarith [norm_sub_le (F w x) (F c x),(hB hw).1 x,(hB (Metric.mem_ball_self hR)).1 x]

end Liu
