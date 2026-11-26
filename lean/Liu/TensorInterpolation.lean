import Liu.ChebyshevApproximation

noncomputable section
open Set Real Polynomial
namespace Liu

def cardinalSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j : Fin (n+1), ‖(Lagrange.basis Finset.univ (firstKindNode n) j).eval (x:ℂ)‖

/-- Evaluation of the tensor interpolant in the order ξ₁, ξ₂, ξ₃. -/
def tensorFirstKind (n₁ n₂ n₃ : ℕ) (F : ℂ → ℂ → ℂ → ℂ) (x y z : ℂ) : ℂ :=
  (firstKindInterpolant n₃ (fun Z => (firstKindInterpolant n₂ (fun Y =>
    (firstKindInterpolant n₁ (fun X => F X Y Z)).eval x)).eval y)).eval z

private theorem firstKind_stability (n : ℕ) (x : ℝ) (f g : ℂ → ℂ) {M : ℝ}
    (h : ∀ j : Fin (n+1), ‖f (firstKindNode n j)-g (firstKindNode n j)‖≤M) :
    ‖(firstKindInterpolant n f).eval (x:ℂ)-(firstKindInterpolant n g).eval (x:ℂ)‖ ≤ cardinalSum n x*M := by
  rw [firstKind_eval_sum,firstKind_eval_sum,←Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  unfold cardinalSum
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [←sub_mul,norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_left (h j) (norm_nonneg _)

theorem firstKind_tensor_error {F : ℂ → ℂ → ℂ → ℂ} (n₁ n₂ n₃ : ℕ)
    {r₁ r₂ r₃ M₁ M₂ M₃ : ℝ} (h₁ : 1<r₁) (h₂ : 1<r₂) (h₃ : 1<r₃)
    (last : ∀ x∈Icc (-1:ℝ) 1, ∀ y∈Icc (-1:ℝ) 1,
      AnalyticOnNhd ℂ (F x y) (bernsteinEllipse r₃) ∧ ∀ Z∈bernsteinEllipse r₃, ‖F x y Z‖≤M₃)
    (middle : ∀ x∈Icc (-1:ℝ) 1, ∀ j : Fin (n₃+1),
      AnalyticOnNhd ℂ (fun Y => F x Y (firstKindNode n₃ j)) (bernsteinEllipse r₂) ∧
        ∀ Y∈bernsteinEllipse r₂, ‖F x Y (firstKindNode n₃ j)‖≤M₂)
    (first : ∀ y∈Icc (-1:ℝ) 1, ∀ j : Fin (n₃+1),
      AnalyticOnNhd ℂ (fun X => F X y (firstKindNode n₃ j)) (bernsteinEllipse r₁) ∧
        ∀ X∈bernsteinEllipse r₁, ‖F X y (firstKindNode n₃ j)‖≤M₁)
    {x y z : ℝ} (hx : x∈Icc (-1:ℝ) 1) (hy : y∈Icc (-1:ℝ) 1) (hz : z∈Icc (-1:ℝ) 1) :
    let E₁ := 4*M₁/(r₁^n₁*(r₁-1))
    let E₂ := 4*M₂/(r₂^n₂*(r₂-1))
    let E₃ := 4*M₃/(r₃^n₃*(r₃-1))
    ‖F x y z-tensorFirstKind n₁ n₂ n₃ F x y z‖≤
      E₃+cardinalSum n₃ z*E₂+cardinalSum n₃ z*cardinalSum n₂ y*E₁ := by
  let P := fun (n : ℕ) (w : ℝ) (f : ℂ → ℂ) => (firstKindInterpolant n f).eval (w:ℂ)
  let A := F x y
  let B := fun Z => P n₂ y (fun Y => F x Y Z)
  let D := fun Z => P n₂ y (fun Y => P n₁ x (fun X => F X Y Z))
  let E := fun (n : ℕ) (M r : ℝ) => 4*M/(r^n*(r-1))
  have ha : ‖F x y z-P n₃ z A‖≤E n₃ M₃ r₃ :=
    firstKind_ellipse_error h₃ (last x hx y hy).1 (last x hx y hy).2 n₃ hz
  have hb : ‖P n₃ z A-P n₃ z B‖≤cardinalSum n₃ z*E n₂ M₂ r₂ :=
    firstKind_stability n₃ z A B (fun j => firstKind_ellipse_error h₂ (middle x hx j).1 (middle x hx j).2 n₂ hy)
  have hd : ‖P n₃ z B-P n₃ z D‖≤cardinalSum n₃ z*(cardinalSum n₂ y*E n₁ M₁ r₁) := by
    apply firstKind_stability
    intro j
    apply firstKind_stability
    intro i
    let v := cos (firstKindAngle n₂ i)
    have hv : v∈Icc (-1:ℝ) 1 := ⟨neg_one_le_cos _,cos_le_one _⟩
    exact firstKind_ellipse_error h₁ (first v hv j).1 (first v hv j).2 n₁ hx
  change ‖F x y z-P n₃ z D‖≤_
  apply (norm_sub_le_norm_sub_add_norm_sub _ (P n₃ z A) _).trans
  have htri := norm_sub_le_norm_sub_add_norm_sub (P n₃ z A) (P n₃ z B) (P n₃ z D)
  change _≤E n₃ M₃ r₃+cardinalSum n₃ z*E n₂ M₂ r₂+cardinalSum n₃ z*cardinalSum n₂ y*E n₁ M₁ r₁
  nlinarith only [ha,hb,hd,htri]

end Liu
