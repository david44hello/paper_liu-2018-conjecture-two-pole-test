import Liu.Gluing

noncomputable section
open Set MeasureTheory
namespace Liu.Certificate

def smallMass (s : ℝ) : ℝ := min (normalMass s) (1-normalMass s)

/-- Pointwise absolute-flux estimate of Lemma 5.4. -/
def smallDepthEstimate : Prop :=
  ∀ s γ t : ℝ, γ ∈ Icc 0 (Real.pi/2) → 0 < t → t ≤ 1/4 →
    |flux s γ t| ≤ 2^34/(smallMass s)^2 * (1 + Real.log (1/t))

/-- The logarithmic coefficient in Lemma E.4 is fixed before the depth varies. -/
def mixedEdgeEstimate : Prop :=
  ∀ s γ : ℝ, γ ∈ Icc 0 (Real.pi/2) → 0 < Real.sin γ →
    ∃ c : ℝ, |c| ≤ 64/(Real.sin γ)^4 ∧ ∀ t : ℝ, 0 < t → t ≤ 1/4 →
      |flux s γ t - c * Real.log (1/t)| ≤ 4096 / ((normalMass s)^2 * (Real.sin γ)^8)

theorem normalMass_pos (s : ℝ) : 0 < normalMass s := by unfold normalMass; positivity

theorem normalMass_antitone : Antitone normalMass := by
  intro x y h
  unfold normalMass
  exact one_div_le_one_div_of_le (by positivity) (by gcongr)

theorem complement_normalMass (s : ℝ) : 1-normalMass s = normalMass (-s) := by
  have hp := Real.exp_pos s
  unfold normalMass
  rw [Real.exp_neg]
  field_simp
  ring

theorem Box.mass_bounds {b : Box} {s γ : ℝ} (h : b.contains s γ) :
    b.aMin ≤ normalMass s ∧ b.muMin ≤ smallMass s := by
  obtain ⟨hlo,hhi,_,_⟩ := h
  refine ⟨normalMass_antitone hhi, ?_⟩
  change normalMass (b.maxMassLog:ℝ) ≤ min (normalMass s) (1-normalMass s)
  rw [complement_normalMass]
  apply le_min <;> apply normalMass_antitone
  · unfold Box.maxMassLog
    push_cast
    exact hhi.trans (le_max_left _ _)
  · unfold Box.maxMassLog
    push_cast
    exact (neg_le_neg hlo).trans (le_max_right _ _)

theorem Box.beta_nonneg {b : Box} (hb : b ∈ boxes) : 0 ≤ b.beta := by
  have ht := (certified_numeric_bounds hb).2.1
  have logpos : 0 ≤ Real.log (1/b.depth) := Real.log_nonneg ((one_le_div b.depth_pos).2 (by linarith))
  unfold Box.beta Box.generalBeta Box.mixedBeta
  have hd := b.depth_pos
  split <;> first | positivity | exact le_min (by positivity) (by positivity)

theorem prefix_of_estimates (h54 : smallDepthEstimate) (hE4 : mixedEdgeEstimate)
    (hflux : fluxIdentity) : prefixProperty := by
  intro b hb s γ hin hg u hu huv
  obtain ⟨ha,hμ⟩ := b.mass_bounds hin
  have hμpos : 0 < b.muMin := by unfold Box.muMin; positivity
  have hap : 0 < b.aMin := normalMass_pos _
  have hv := (certified_numeric_bounds hb).2.1
  have hi := (hflux s γ hg u b.depth hu huv).1.abs
  have ht : b.depth ≤ 1 := by linarith
  have logpos (t : ℝ) (h : t ∈ Icc u b.depth) : 0 ≤ Real.log (1/t) :=
    Real.log_nonneg ((one_le_div (hu.trans_le h.1)).2 (h.2.trans ht))
  have general : (∫ t in u..b.depth, |flux s γ t|) ≤ b.generalBeta := by
    let A := (2:ℝ)^34/b.muMin^2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have p (t : ℝ) (h : t ∈ Icc u b.depth) : |flux s γ t| ≤ A * Real.log (1/t) + A := by
      have c : (2:ℝ)^34 / (smallMass s)^2 ≤ A := by dsimp [A]; gcongr
      calc
        _ ≤ _ := h54 s γ t hg (hu.trans_le h.1) (h.2.trans hv)
        _ ≤ A * (1+Real.log (1/t)) := mul_le_mul_of_nonneg_right c (by linarith [logpos t h])
        _ = _ := by ring
    have q := log_majorant_integral hu huv ht hA hA hi p
    convert q using 1 <;> dsimp [A,Box.generalBeta] <;> ring
  unfold Box.beta
  split
  next hangle =>
    apply le_min general
    let S := Real.sin (b.chart.angle b.yLo)
    have hs0 : 0 < S := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hin.2.2.1,hg.2,Real.pi_pos])
    have hsin : S ≤ Real.sin γ := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) hg.2 hin.2.2.1
    obtain ⟨c,hc,herr⟩ := hE4 s γ hg (hs0.trans_le hsin)
    let A := 64/S^4
    let B := 4096/(b.aMin^2*S^8)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have cA : |c| ≤ A := hc.trans (by dsimp [A]; gcongr)
    have cB : 4096/((normalMass s)^2 * (Real.sin γ)^8) ≤ B := by dsimp [B]; gcongr
    have p (t : ℝ) (h : t ∈ Icc u b.depth) : |flux s γ t| ≤ A * Real.log (1/t) + B := by
      have herr' := (herr t (hu.trans_le h.1) (h.2.trans hv)).trans cB
      have hlog := logpos t h
      have tri := abs_add_le (flux s γ t-c*Real.log (1/t)) (c*Real.log (1/t))
      rw [sub_add_cancel,abs_mul,abs_of_nonneg hlog] at tri
      linarith [mul_le_mul_of_nonneg_right cA hlog]
    exact log_majorant_integral hu huv ht hA hB hi p
  next => exact general

end Liu.Certificate
