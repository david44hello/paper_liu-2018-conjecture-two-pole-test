import Liu.Cover

namespace Liu.Certificate

/-- The central cell of the corner band, described by its published rational edges. -/
def central (b : Box) : Bool := decide
  (b.chart = .corner ∧ b.yLo = 0 ∧ b.yHi = 1/1048576 ∧
    b.cell.sLo = -(25/27) ∧ b.cell.sHi = 25/27)

def withoutCentral : List Box := boxes.filter fun b => !central b

def atOrigin (b : Box) : Bool := decide
  (b.chart ≠ .logAngle ∧ b.yLo ≤ 0 ∧ 0 ≤ b.yHi ∧ b.cell.sLo ≤ 0 ∧ 0 ≤ b.cell.sHi)

theorem contains_origin_iff (b : Box) : b.contains 0 0 ↔ atOrigin b = true := by
  rcases b with ⟨chart, yl, yh, c⟩
  cases chart <;> simp [Box.contains, Chart.angle, atOrigin, Real.exp_pos, not_le_of_gt,
    and_assoc, and_left_comm, and_comm]

theorem withoutCentral_length : withoutCentral.length = 167 := by decide +kernel

theorem withoutCentral_any_false : withoutCentral.any atOrigin = false := by decide +kernel

theorem withoutCentral_misses_origin : ¬ ∃ b ∈ withoutCentral, b.contains 0 0 := by
  intro ⟨b,hb,h⟩
  have yes : withoutCentral.any atOrigin = true := List.any_eq_true.mpr
    ⟨b,hb,(contains_origin_iff b).mp h⟩
  simp [withoutCentral_any_false] at yes

end Liu.Certificate
