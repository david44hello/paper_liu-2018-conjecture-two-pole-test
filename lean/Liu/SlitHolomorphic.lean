module

public import Liu.CutDomain
public import Liu.PairedFlux

@[expose] public section

noncomputable section
open Set Filter Complex
open scoped Topology
namespace Liu

/-- The allowed arguments of the lower-node and upper-partner logarithms. -/
def sideOk (s : Bool) (z : ℂ) : Prop := z.re≠0 ∨ (if s then 0 < z.im else z.im < 0)

theorem sideOk_ne_zero {s : Bool} {z : ℂ} (h : sideOk s z) : z≠0 := by
  intro e; subst z; cases s <;> simp [sideOk] at h

theorem sideLog_diff_on_cut_complement {s : Bool} {z : ℂ} (h : sideOk s z) : DifferentiableAt ℂ (sideLog s) z := by
  cases s
  · have H : I*z∈slitPlane := by
      rw [mem_slitPlane_iff]
      rcases h with hl|hr
      · right; simpa [Complex.mul_im] using hl
      · left; simpa [Complex.mul_re] using (show z.im < 0 from hr)
    exact (((differentiableAt_id (𝕜:=ℂ) (x:=z)).const_mul I).clog H).sub_const _
  · have H : -I*z∈slitPlane := by
      rw [mem_slitPlane_iff]
      rcases h with hl|hr
      · right; simpa [Complex.mul_im] using hl
      · left; simpa [Complex.mul_re] using (show 0 < z.im from hr)
    exact (((differentiableAt_id (𝕜:=ℂ) (x:=z)).const_mul (-I)).clog H).add_const _

theorem offCuts_iff_sideOk (P Q : Fin 3 → ℂ) (z : ℂ) :
    z∈offCuts P Q ↔ (∀ i, sideOk true (z-P i)) ∧ ∀ j, sideOk false (z-Q j) := by
  classical
  simp only [offCuts,cutHeights,mem_setOf_eq,sideOk,sub_re,sub_im,if_true,Bool.false_eq_true,if_false,
    sub_ne_zero,sub_pos,sub_neg,←imp_iff_not_or]

theorem clearance_iff (p q : ℂ) : ¬rayCollision p q ↔ sideOk false (p-q) ∧ sideOk true (q-p) := by
  unfold rayCollision sideOk
  simp only [sub_re,sub_im,sub_ne_zero,sub_neg,sub_pos,Bool.false_eq_true,if_false,if_true]
  by_cases e : p.re=q.re <;> simp [e,Ne.symm,not_and_or]

/-- Holomorphic pullback of a term in the observation point and both
parameters on the stated vertical-cut branches. -/
theorem tailTerm_diff_pull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s : Bool} {p q z : E → ℂ} {w : E}
    (dp : DifferentiableAt ℂ p w) (dq : DifferentiableAt ℂ q w) (dz : DifferentiableAt ℂ z w)
    (zp : sideOk s (z w-p w)) (zq : sideOk (!s) (z w-q w))
    (pq : sideOk (!s) (p w-q w)) (qp : sideOk s (q w-p w)) :
    DifferentiableAt ℂ (fun w => tailTerm s (p w) (q w) (z w)) w := by
  have h₁ := sideLog_diff_on_cut_complement zp
  have h₂ := sideLog_diff_on_cut_complement zq
  have h₃ := sideLog_diff_on_cut_complement pq
  have h₄ := sideLog_diff_on_cut_complement qp
  have hn := sideOk_ne_zero zp
  have hn' := sideOk_ne_zero zq
  unfold tailTerm; fun_prop (disch := assumption)

theorem totalDensity_diff_pull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P Q : Fin 3 → E → ℂ} {a b z : E → ℂ} {w : E}
    (dp : ∀ j, DifferentiableAt ℂ (P j) w) (dq : ∀ j, DifferentiableAt ℂ (Q j) w)
    (da : DifferentiableAt ℂ a w) (db : DifferentiableAt ℂ b w) (dz : DifferentiableAt ℂ z w)
    (h : z w∈offCuts (fun j => P j w) (fun j => Q j w))
    (hc : ∀ i j, ¬rayCollision (P i w) (Q j w)) :
    DifferentiableAt ℂ (fun t => totalDensity (fun j => P j t) (fun j => Q j t) (a t) (b t) (z t)) w := by
  obtain ⟨hp,hq⟩ := (offCuts_iff_sideOk _ _ _).mp h
  have H (i j : Fin 3) := tailTerm_diff_pull (s:=true) (dp i) (dq j) dz (hp i) (hq j)
    ((clearance_iff ..).mp (hc i j)).1 ((clearance_iff ..).mp (hc i j)).2
  have H' (i j : Fin 3) := tailTerm_diff_pull (s:=false) (dq i) (dp j) dz (hq i) (hp j)
    ((clearance_iff ..).mp (hc j i)).2 ((clearance_iff ..).mp (hc j i)).1
  have V (i : Fin 3) : DifferentiableAt ℂ (fun t => tailPole (P i t) (z t)) w :=
    ((dz.sub (dp i)).inv (sideOk_ne_zero (hp i))).neg
  have V' (i : Fin 3) : DifferentiableAt ℂ (fun t => tailPole (Q i t) (z t)) w :=
    ((dz.sub (dq i)).inv (sideOk_ne_zero (hq i))).neg
  have side (s : Bool) (A B : Fin 3 → E → ℂ)
      (K : ∀ i j, DifferentiableAt ℂ (fun t => tailTerm s (A i t) (B j t) (z t)) w) :
      DifferentiableAt ℂ (fun t => tailSide s (fun i => A i t) (fun j => B j t) (a t) (b t) (z t)) w := by
    let k := fieldCoefficient s
    simpa only [tailSide,tailSingle,tailCross,Fin.castSucc_zero,show (1:Fin 2).castSucc=(1:Fin 3) by decide,k] using
      ((da.fun_mul ((K 0 0).const_mul k)).fun_add (db.fun_mul ((K 1 1).const_mul k))).fun_add
        (((da.fun_mul ((K 0 1).fun_sub (K 0 2))).fun_add (db.fun_mul ((K 1 0).fun_sub (K 1 2)))).const_mul k)
  have A := side true P Q H
  have B := side false Q P H'
  have C := (da.fun_mul (V 0)).fun_add (db.fun_mul (V 1))
  have D := (da.fun_mul (V' 0)).fun_add (db.fun_mul (V' 1))
  exact (A.fun_mul B).fun_sub ((C.const_mul (k₀:ℂ)).fun_mul D)

end Liu
