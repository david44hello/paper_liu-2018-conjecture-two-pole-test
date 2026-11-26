import Liu.Beta

namespace Liu.Certificate

private def validBox (b : Box) : Bool := decide (
  |b.maxMassLog| ≤ 16 ∧ |b.cell.sHi| ≤ 16 ∧
  (b.chart = .largeAngle → b.yLo = 53/100 ∨ b.yLo = 1) ∧
  b.betaMajor ≤ 1/2000 ∧ 285/10000 + b.betaMajor < b.safeLower ∧
  b.depthUpper ≤ 1/4)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
private theorem ledger_checked : boxes.all validBox = true := by decide +kernel

theorem certified_numeric_bounds {b : Box} (hb : b ∈ boxes) :
    0 < b.depth ∧ b.depth ≤ 1/4 ∧ b.beta ≤ 1/2000 ∧
    285/10000 + b.beta < (b.safeLower:ℝ) := by
  have h := List.all_eq_true.mp ledger_checked b hb
  simp only [validBox,decide_eq_true_eq] at h
  obtain ⟨hm,hs,hy,hbeta,hgap,hu⟩ := h
  have hle := b.beta_le_major hm hs hy
  have v : (b.depthUpper:ℝ) ≤ 1/4 := by simpa using (Rat.cast_le (K := ℝ)).mpr hu
  have v₁ : (b.betaMajor:ℝ) ≤ 1/2000 := by simpa using (Rat.cast_le (K := ℝ)).mpr hbeta
  have v₂ : (285/10000:ℝ) + b.betaMajor < b.safeLower := by simpa using (Rat.cast_lt (K := ℝ)).mpr hgap
  exact ⟨b.depth_pos,b.depth_le_upper.trans v,hle.trans v₁,by linarith⟩

end Liu.Certificate
