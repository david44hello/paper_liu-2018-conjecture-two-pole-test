import Liu.BetaLedger
import Liu.LogIntegral

open MeasureTheory Set Filter
noncomputable section
namespace Liu.Certificate

/-- Proposition 6.1 with the fixed 168 depth / lower-bound pairs of the certificate. -/
def boxBounds : Prop :=
  ∀ b ∈ boxes, ∀ s γ : ℝ, b.contains s γ → γ ≤ Real.pi/2 →
    (∀ u : ℝ, b.depth ≤ u → 0 < margin s γ u) ∧
      (b.safeLower:ℝ) ≤ margin s γ b.depth

/-- The finite-depth identity of Lemma 5.1, with the actual Green-potential flux. -/
def fluxIdentity : Prop :=
  ∀ s γ : ℝ, γ ∈ Icc 0 (Real.pi/2) → ∀ u v : ℝ, 0 < u → u ≤ v →
    IntervalIntegrable (flux s γ) volume u v ∧
    margin s γ u = margin s γ v - ∫ t in u..v, flux s γ t

/-- The separate small-depth analytic conclusion before Proposition 6.1. -/
def prefixProperty : Prop :=
  ∀ b ∈ boxes, ∀ s γ : ℝ, b.contains s γ → γ ∈ Icc 0 (Real.pi/2) →
    ∀ u : ℝ, 0 < u → u ≤ b.depth →
      (∫ t in u..b.depth, |flux s γ t|) ≤ b.beta

theorem normalized_margin_pos (hbox : boxBounds) (hflux : fluxIdentity)
    (hprefix : prefixProperty) {s γ u : ℝ} (hs : s ∈ Icc (-(25/3:ℝ)) (25/3))
    (hg : γ ∈ Icc 0 (Real.pi/2)) (hu : 0 < u) : 0 < margin s γ u := by
  obtain ⟨b,hb,hin⟩ := cover hs.1 hs.2 hg.1 hg.2
  obtain ⟨hdeep,hedge⟩ := hbox b hb s γ hin hg.2
  by_cases h : b.depth ≤ u
  · exact hdeep u h
  · have huv := (lt_of_not_ge h).le
    obtain ⟨_,hid⟩ := hflux s γ hg u b.depth hu huv
    have hβ := hprefix b hb s γ hin hg u hu huv
    have hnum := (certified_numeric_bounds hb).2.2.2
    have hbound := intervalIntegral.abs_integral_le_integral_abs
      (f := flux s γ) (μ := volume) huv
    rw [hid]
    linarith [le_abs_self (∫ t in u..b.depth,flux s γ t)]

theorem prefix_sup_bound (hp : prefixProperty) {b : Box} (hb : b ∈ boxes)
    {s γ : ℝ} (hin : b.contains s γ) (hg : γ ∈ Icc 0 (Real.pi/2)) :
    let values := (fun u => ∫ t in u..b.depth, |flux s γ t|) '' Ioc 0 b.depth
    values.Nonempty ∧ BddAbove values ∧ sSup values ≤ b.beta := by
  dsimp only
  have ne : ((fun u => ∫ t in u..b.depth, |flux s γ t|) '' Ioc 0 b.depth).Nonempty :=
    ⟨_,b.depth,⟨b.depth_pos,le_rfl⟩,rfl⟩
  have upper : ∀ x ∈ (fun u => ∫ t in u..b.depth, |flux s γ t|) '' Ioc 0 b.depth,
      x ≤ b.beta := by
    rintro x ⟨u,hu,rfl⟩
    exact hp b hb s γ hin hg u hu.1 hu.2
  exact ⟨ne,⟨b.beta,upper⟩,csSup_le ne upper⟩

end Liu.Certificate
