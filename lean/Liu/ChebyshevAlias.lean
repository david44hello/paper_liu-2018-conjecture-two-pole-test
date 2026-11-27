module

public import Mathlib

@[expose] public section

noncomputable section
open Set Real Polynomial Polynomial.Chebyshev
namespace Liu

def firstKindAngle (n : ℕ) (j : Fin (n+1)) : ℝ :=
  (2*(j:ℝ)+1)*π/(2*((n:ℝ)+1))

def firstKindNode (n : ℕ) (j : Fin (n+1)) : ℂ := (cos (firstKindAngle n j):ℝ)

def firstKindInterpolant (n : ℕ) (f : ℂ → ℂ) : Polynomial ℂ :=
  Lagrange.interpolate Finset.univ (firstKindNode n) (fun j => f (firstKindNode n j))

private theorem angle_range (n : ℕ) (j : Fin (n+1)) : firstKindAngle n j∈Icc 0 π := by
  have hj : (j:ℝ)<(n:ℝ)+1 := by exact_mod_cast j.isLt
  have hn : 0<2*((n:ℝ)+1) := by positivity
  constructor
  · unfold firstKindAngle; positivity
  · unfold firstKindAngle; rw [div_le_iff₀ hn]
    have hj' : (j:ℝ)≤n := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    nlinarith only [mul_le_mul_of_nonneg_right hj' pi_pos.le,pi_pos]

theorem firstKindNode_injective (n : ℕ) : Function.Injective (firstKindNode n) := by
  intro j k h
  have he := Complex.ofReal_injective h
  have eq := injOn_cos (angle_range n j) (angle_range n k) he
  unfold firstKindAngle at eq
  have hd : (2:ℝ)*((n:ℝ)+1)≠0 := by positivity
  have hh := (div_left_inj' hd).mp eq
  have h' := mul_right_cancel₀ pi_ne_zero hh
  apply Fin.ext; exact_mod_cast (show (j:ℝ)=(k:ℝ) by linarith)

private theorem modal_value (k : ℕ) (θ : ℝ) :
    (T ℂ k).eval ((cos θ:ℝ):ℂ)=((cos ((k:ℝ)*θ):ℝ):ℂ) := by
  rw [Complex.ofReal_cos,T_complex_cos]
  push_cast; rfl

private theorem modal_norm (k : ℕ) {x : ℝ} (hx : x∈Icc (-1:ℝ) 1) :
    ‖(T ℂ k).eval (x:ℂ)‖≤1 := by
  obtain ⟨θ,_,he⟩ := surjOn_cos hx
  rw [←he,modal_value,Complex.norm_real,Real.norm_eq_abs]
  exact abs_cos_le_one _

private theorem node_halfturn (n : ℕ) (j : Fin (n+1)) :
    ((2*(n+1):ℕ):ℝ)*firstKindAngle n j=(2*(j:ℝ)+1)*π := by
  unfold firstKindAngle; push_cast
  field_simp [show (n:ℝ)+1≠0 by positivity]

private theorem cos_step (n k : ℕ) (j : Fin (n+1)) :
    cos (((2*(n+1)+k:ℕ):ℝ)*firstKindAngle n j)= -cos ((k:ℝ)*firstKindAngle n j) := by
  let θ := firstKindAngle n j
  have he : (((2*(n+1)+k:ℕ):ℝ)*θ)= (k:ℝ)*θ+π+(j:ℝ)*(2*π) := by
    rw [Nat.cast_add,add_mul,node_halfturn]; ring
  rw [he,cos_add_nat_mul_two_pi,cos_add_pi]

private theorem cos_reverse (n k : ℕ) (hk : k≤2*(n+1)) (j : Fin (n+1)) :
    cos (((2*(n+1)-k:ℕ):ℝ)*firstKindAngle n j)= -cos ((k:ℝ)*firstKindAngle n j) := by
  let θ := firstKindAngle n j
  have he : (((2*(n+1)-k:ℕ):ℝ)*θ)= -((k:ℝ)*θ)+π+(j:ℝ)*(2*π) := by
    rw [Nat.cast_sub hk,sub_mul,node_halfturn]; ring
  rw [he,cos_add_nat_mul_two_pi,cos_add_pi,cos_neg]

/-- Every sampled Chebyshev mode interpolates to a polynomial of magnitude
at most one on the real interval, uniformly in the frequency. -/
theorem firstKind_alias (n k : ℕ) :
    ∃ P : Polynomial ℂ, P.degree<(n+1:ℕ) ∧
      (∀ j : Fin (n+1), P.eval (firstKindNode n j)=(T ℂ k).eval (firstKindNode n j)) ∧
      ∀ x : ℝ, x∈Icc (-1:ℝ) 1 → ‖P.eval (x:ℂ)‖≤1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hl : k < n+1
    · refine ⟨T ℂ k,?_,fun _ => rfl,fun _ h => modal_norm k h⟩
      rw [degree_T]; exact_mod_cast hl
    by_cases hm : k=n+1
    · subst k
      refine ⟨0,by simp,?_,by simp⟩
      intro j
      rw [firstKindNode,modal_value]
      have he := cos_reverse n (n+1) (by omega) j
      rw [show 2*(n+1)-(n+1)=n+1 by omega] at he
      rw [show cos (((n+1:ℕ):ℝ)*firstKindAngle n j)=0 by linarith]
      simp
    by_cases hh : k≤2*(n+1)
    · let l := 2*(n+1)-k
      have hlt : l<k := by dsimp [l]; omega
      obtain ⟨P,hP,he,hb⟩ := ih l hlt
      refine ⟨-P,by simpa using hP,?_,fun x hx => by simpa using hb x hx⟩
      intro j
      rw [eval_neg,he j,firstKindNode,modal_value,modal_value]
      rw [show cos ((l:ℝ)*firstKindAngle n j)= -cos ((k:ℝ)*firstKindAngle n j) from cos_reverse n k hh j]
      simp
    · let l := k-2*(n+1)
      have hlt : l<k := by dsimp [l]; omega
      obtain ⟨P,hP,he,hb⟩ := ih l hlt
      refine ⟨-P,by simpa using hP,?_,fun x hx => by simpa using hb x hx⟩
      intro j
      rw [eval_neg,he j,firstKindNode,modal_value,modal_value]
      have hs := cos_step n l j
      rw [show 2*(n+1)+l=k by dsimp [l]; omega] at hs
      simp only [hs,Complex.ofReal_neg]

theorem firstKind_interpolated_mode (n k : ℕ) {x : ℝ} (hx : x∈Icc (-1:ℝ) 1) :
    ‖(firstKindInterpolant n (fun z => (T ℂ k).eval z)).eval (x:ℂ)‖≤1 := by
  obtain ⟨P,hP,hn,hb⟩ := firstKind_alias n k
  have he := Lagrange.eq_interpolate_of_eval_eq (s:=Finset.univ) (fun i => (T ℂ k).eval (firstKindNode n i))
    (firstKindNode_injective n).injOn (by simpa using hP) (fun i _ => hn i)
  rw [firstKindInterpolant,←he]
  exact hb x hx

end Liu
