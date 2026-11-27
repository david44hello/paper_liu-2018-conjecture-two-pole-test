module

public import Liu.VerticalLog

@[expose] public section

noncomputable section
open Set Real Complex
namespace Liu

/-- Lower-side logs have downward cuts and upper-side logs have upward cuts.
Switching side exchanges the two branches, as in the conjugate field. -/
def sideLog (lower : Bool) (w : ℂ) := if lower then lowerNodeLog w else upperNodeLog w

def tailTerm (lower : Bool) (p q z : ℂ) : ℂ :=
  (sideLog (!lower) (z-q)-sideLog (!lower) (p-q))/(z-p) -
    (sideLog lower (z-p)-sideLog lower (q-p))/(z-q)

def constantLogCost (lower : Bool) (p q : ℂ) : ℝ :=
  ‖sideLog (!lower) (p-q)‖+‖sideLog lower (q-p)‖

def sideLogCost (lower : Bool) (P Q : Fin 3 → ℂ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 3, constantLogCost lower (P i.castSucc) (Q j)

def totalLogCost (P Q : Fin 3 → ℂ) : ℝ := sideLogCost true P Q + sideLogCost false Q P

def tailUpsilon (P Q : Fin 3 → ℂ) (x : ℝ) : ℝ := Real.log (3*|x|/2)+π+totalLogCost P Q

theorem sideLogCost_nonneg (s : Bool) (P Q : Fin 3 → ℂ) : 0 ≤ sideLogCost s P Q :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem constantLogCost_le (s : Bool) (P Q : Fin 3 → ℂ) (i : Fin 2) (j : Fin 3) :
    constantLogCost s (P i.castSucc) (Q j) ≤ sideLogCost s P Q := by
  have h (k : Fin 2) (l : Fin 3) : 0≤constantLogCost s (P k.castSucc) (Q l) :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  exact (Finset.single_le_sum (fun l _ => h i l) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => h k l) (Finset.mem_univ i))

theorem tailTerm_bound {s : Bool} {X x C : ℝ} {p q : ℂ}
    (hX : 10^18≤X) (hx : X≤|x|) (hp : 4*‖p‖<X) (hq : 4*‖q‖<X) (hc : constantLogCost s p q ≤ C) :
    ‖tailTerm s p q (x:ℂ)‖ ≤ 4*(Real.log (3*|x|/2)+π+C)/|x| := by
  have hl (u : Bool) (c : ℂ) (hs : 4*‖c‖<X) : ‖sideLog u ((x:ℂ)-c)‖≤Real.log (3*|x|/2)+π := by
    have H := (vertical_log_tail hX hs hx).2.2
    cases u
    · exact H.2
    · exact H.1
  let A := Real.log (3*|x|/2)+π+C
  have hC₁ : ‖sideLog (!s) (p-q)‖≤C := (le_add_of_nonneg_right (norm_nonneg _)).trans hc
  have hC₂ : ‖sideLog s (q-p)‖≤C := (le_add_of_nonneg_left (norm_nonneg _)).trans hc
  have h₁ := (norm_sub_le (sideLog (!s) ((x:ℂ)-q)) (sideLog (!s) (p-q))).trans (add_le_add (hl _ q hq) hC₁)
  have h₂ := (norm_sub_le (sideLog s ((x:ℂ)-p)) (sideLog s (q-p))).trans (add_le_add (hl _ p hp) hC₂)
  have ha : 0≤A := (norm_nonneg _).trans h₁
  have hx₀ : 0 < |x|/2 := by linarith
  have d₁ := div_le_div₀ ha h₁ hx₀ (vertical_log_tail hX hp hx).1
  have d₂ := div_le_div₀ ha h₂ hx₀ (vertical_log_tail hX hq hx).1
  unfold tailTerm
  apply (norm_sub_le ..).trans
  simp only [norm_div]
  apply (add_le_add d₁ d₂).trans_eq
  dsimp [A]
  ring

def fieldCoefficient (lower : Bool) : ℂ := if lower then I/2 else -I/2

/-- The isolated fields and the four mixed terms in the two-pole formula. -/
def tailSingle (s : Bool) (P Q : Fin 3 → ℂ) (i : Fin 2) (z : ℂ) : ℂ :=
  fieldCoefficient s * tailTerm s (P i.castSucc) (Q i.castSucc) z

def tailCross (s : Bool) (P Q : Fin 3 → ℂ) (a b z : ℂ) : ℂ :=
  fieldCoefficient s * (a*(tailTerm s (P 0) (Q 1) z-tailTerm s (P 0) (Q 2) z) +
    b*(tailTerm s (P 1) (Q 0) z-tailTerm s (P 1) (Q 2) z))

def tailSide (s : Bool) (P Q : Fin 3 → ℂ) (a b z : ℂ) : ℂ :=
  a*tailSingle s P Q 0 z+b*tailSingle s P Q 1 z+tailCross s P Q a b z

def tailPole (p z : ℂ) : ℂ := -(z-p)⁻¹

/-- The field and Pick products with both isolated pole contributions subtracted. -/
def subtractedTail (P Q : Fin 3 → ℂ) (a b z : ℂ) : ℂ :=
  let S := fun p => tailPole p z
  let H := fun i : Fin 2 => tailSingle true P Q i z*tailSingle false Q P i z -
    (k₀:ℂ)*S (P i.castSucc)*S (Q i.castSucc)
  tailSide true P Q a b z * tailSide false Q P a b z -
    (k₀:ℂ)*(a*S (P 0)+b*S (P 1))*(a*S (Q 0)+b*S (Q 1)) - a^2*H 0-b^2*H 1

end Liu
