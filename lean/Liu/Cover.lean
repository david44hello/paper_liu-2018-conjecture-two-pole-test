module

public import Liu.BoxData
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

namespace Liu.Certificate

/-- Walk a finite list of rational closed intervals from left to right. -/
def coversRange {α : Type*} (lo hi : α → ℚ) (right : ℚ) : List α → ℚ → Bool
  | [], _ => false
  | a :: rest, left =>
    decide (lo a ≤ left) && (decide (right ≤ hi a) || coversRange lo hi right rest (hi a))

theorem coversRange_sound {α : Type*} {lo hi : α → ℚ} {left right : ℚ}
    {xs : List α} {x : ℝ} (cert : coversRange lo hi right xs left = true)
    (hleft : (left : ℝ) ≤ x) (hright : x ≤ (right : ℝ)) :
    ∃ a ∈ xs, (lo a : ℝ) ≤ x ∧ x ≤ (hi a : ℝ) := by
  induction xs generalizing left with
  | nil => simp [coversRange] at cert
  | cons a rest ih =>
    simp only [coversRange, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at cert
    have low : (lo a : ℝ) ≤ (left : ℝ) := by exact_mod_cast cert.1
    by_cases hx : x ≤ (hi a : ℝ)
    · exact ⟨a, List.mem_cons_self, low.trans hleft, hx⟩
    · rcases cert.2 with high | tail
      · have h : (right : ℝ) ≤ (hi a : ℝ) := by exact_mod_cast high
        exact (hx (hright.trans h)).elim
      · obtain ⟨b, hb, bounds⟩ := ih tail (le_of_not_ge hx)
        exact ⟨b, List.mem_cons_of_mem _ hb, bounds⟩

/-- Physical overlap between the corner band and the logarithmic bands. -/
theorem corner_seam : Real.exp (-(1483 / 100 : ℝ)) < 1 / (2:ℝ)^20 := by
  have h27 : (27/10:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h : (2:ℝ)^20 < Real.exp (1483/100) := calc
    (2:ℝ)^20 < (27/10:ℝ)^14 := by norm_num
    _ ≤ (Real.exp 1)^14 := by gcongr
    _ = Real.exp (14:ℝ) := by simpa using (Real.exp_nat_mul 1 14).symm
    _ < _ := Real.exp_lt_exp.mpr (by norm_num)
  rw [Real.exp_neg, one_div]
  exact (inv_lt_inv₀ (Real.exp_pos _) (by positivity)).mpr h

/-- Physical overlap between the logarithmic bands and the large-angle bands. -/
theorem large_seam : (53/100:ℝ) < Real.exp (-(63/100:ℝ)) := by
  have h := Real.exp_bound (x := -(63/100:ℝ)) (n := 6) (by norm_num) (by decide)
  have h' := (abs_le.mp h).1
  norm_num [Finset.sum_range_succ, Nat.factorial] at h'
  linarith

theorem physical_top : Real.pi / 2 < 1571 / 1000 := by linarith [Real.pi_lt_d4]

private def bandChecks (chart : Chart) (rs : List Band) : Bool :=
  rs.all fun r => decide (r.chart = chart) &&
    coversRange Cell.sLo Cell.sHi (25/3) r.cells (-(25/3))

private theorem lookup {chart : Chart} {rs : List Band} {l h : ℚ}
    (angles : coversRange Band.yLo Band.yHi h rs l = true)
    (bandsOK : bandChecks chart rs = true)
    {s y : ℝ} (hsl : -(25/3:ℝ) ≤ s) (hsh : s ≤ 25/3)
    (hyl : (l:ℝ) ≤ y) (hyh : y ≤ (h:ℝ)) :
    ∃ r ∈ rs, ∃ c ∈ r.cells, r.chart = chart ∧
      (c.sLo:ℝ) ≤ s ∧ s ≤ c.sHi ∧ (r.yLo:ℝ) ≤ y ∧ y ≤ r.yHi := by
  obtain ⟨r, hr, hlow, hhigh⟩ := coversRange_sound angles hyl hyh
  have row := List.all_eq_true.mp bandsOK r hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at row
  obtain ⟨c, hc, hs1, hs2⟩ := coversRange_sound row.2 (x := s) (by norm_num at * <;> assumption) (by norm_num at * <;> assumption)
  exact ⟨r, hr, c, hc, row.1, hs1, hs2, hlow, hhigh⟩

private theorem box_mem {r : Band} {c : Cell} (hr : r ∈ bands) (hc : c ∈ r.cells) :
    r.box c ∈ boxes :=
  List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨c, hc, rfl⟩⟩

set_option maxHeartbeats 1200000 in
theorem cover {s γ : ℝ} (hs₁ : -(25/3:ℝ) ≤ s) (hs₂ : s ≤ 25/3)
    (hg₁ : 0 ≤ γ) (hg₂ : γ ≤ Real.pi / 2) : ∃ b ∈ boxes, b.contains s γ := by
  by_cases small : γ ≤ 1 / (2:ℝ)^20
  · obtain ⟨r,hr,c,hc,chart,sl,sh,yl,yh⟩ :=
      lookup (rs := cornerBands) (chart := .corner) (l := 0) (h := 1/1048576)
        (by decide +kernel) (by decide +kernel) hs₁ hs₂ (y := γ) (by simpa) (by norm_num at small ⊢; exact small)
    exact ⟨r.box c, box_mem (by simp [bands, hr]) hc, sl, sh,
      by simpa [Band.box, Chart.angle,chart] using yl, by simpa [Band.box, Chart.angle,chart] using yh⟩
  by_cases large : 53/100 ≤ γ
  · obtain ⟨r,hr,c,hc,chart,sl,sh,yl,yh⟩ :=
      lookup (rs := largeBands) (chart := .largeAngle) (l := 53/100) (h := 1571/1000)
        (by decide +kernel) (by decide +kernel) hs₁ hs₂ (y := γ)
        (by norm_num at * <;> assumption) (by norm_num <;> linarith [physical_top])
    exact ⟨r.box c, box_mem (by simp [bands, hr]) hc, sl, sh,
      by simpa [Band.box, Chart.angle,chart] using yl, by simpa [Band.box, Chart.angle,chart] using yh⟩
  · have hg : 0 < γ := lt_trans (by positivity) (lt_of_not_ge small)
    have low : -(1483/100:ℝ) ≤ Real.log γ :=
      (Real.le_log_iff_exp_le hg).2 (corner_seam.le.trans (le_of_not_ge small))
    have high : Real.log γ ≤ -(63/100:ℝ) :=
      (Real.log_le_iff_le_exp hg).2 ((le_of_not_ge large).trans large_seam.le)
    obtain ⟨r,hr,c,hc,chart,sl,sh,yl,yh⟩ :=
      lookup (rs := logBands) (chart := .logAngle) (l := -(1483/100)) (h := -(63/100))
        (by decide +kernel) (by decide +kernel) hs₁ hs₂ (y := Real.log γ) (by norm_num at * <;> assumption) (by norm_num at * <;> assumption)
    exact ⟨r.box c, box_mem (by simp [bands, hr]) hc, sl, sh,
      by simpa [Band.box,Chart.angle,chart,Real.exp_log hg] using Real.exp_le_exp.mpr yl,
      by simpa [Band.box,Chart.angle,chart,Real.exp_log hg] using Real.exp_le_exp.mpr yh⟩

end Liu.Certificate
