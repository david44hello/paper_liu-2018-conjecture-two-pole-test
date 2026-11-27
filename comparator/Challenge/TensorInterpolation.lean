module

public import Challenge.ChebyshevApproximation

@[expose] public section

/- Frozen input: Liu/TensorInterpolation.lean -/
noncomputable section
open Set Real Polynomial
namespace Liu

def cardinalSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j : Fin (n+1), ‖(Lagrange.basis Finset.univ (firstKindNode n) j).eval (x:ℂ)‖

def tensorFirstKind (n₁ n₂ n₃ : ℕ) (F : ℂ → ℂ → ℂ → ℂ) (x y z : ℂ) : ℂ :=
  (firstKindInterpolant n₃ (fun Z => (firstKindInterpolant n₂ (fun Y =>
    (firstKindInterpolant n₁ (fun X => F X Y Z)).eval x)).eval y)).eval z

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
      E₃+cardinalSum n₃ z*E₂+cardinalSum n₃ z*cardinalSum n₂ y*E₁ := by sorry

end Liu
end
