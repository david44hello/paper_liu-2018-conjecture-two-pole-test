module

public import Challenge.TensorInterpolation

@[expose] public section

/- Frozen input: Liu/CitedInterpolation.lean -/
noncomputable section
open Set Real Polynomial
namespace Liu

/-- H4 is a refereed external result for Lemma 6.5. Ibrahimoglu (2016), §3.2, equation (13), DOI 10.1186/s13660-016-1030-3. The theorems that use this scalar bound take it as an explicit argument. -/
def firstKindLebesgueInput : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ x : ℝ, x ∈ Set.Icc (-1:ℝ) 1 →
  let node := fun j : Fin (n+1) =>
    Real.cos ((2*(j:ℝ)+1)*Real.pi/(2*((n:ℝ)+1)))
  (∑ i : Fin (n+1), |(Lagrange.basis Finset.univ node i).eval x|) ≤
    (2/Real.pi)*Real.log ((n:ℝ)+1) + (974/1000:ℝ)

theorem cardinalSum_real (n : ℕ) (x : ℝ) :
    cardinalSum n x=∑ j : Fin (n+1), |(Lagrange.basis Finset.univ
      (fun i => cos (firstKindAngle n i)) j).eval x| := by sorry

theorem firstKind_lebesgue_bound_given (h4 : firstKindLebesgueInput) {n : ℕ} (hn : 1≤n)
    {x : ℝ} (hx : x∈Icc (-1:ℝ) 1) : cardinalSum n x≤1+(2/π)*log ((n:ℝ)+1) := by sorry

theorem tensor_error_given_cited_scalar (h4 : firstKindLebesgueInput) {F : ℂ → ℂ → ℂ → ℂ} (n₁ n₂ n₃ : ℕ)
    (hn₁ : 1≤n₁) (hn₂ : 1≤n₂) (hn₃ : 1≤n₃)
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
    let L := fun n : ℕ => 1+(2/π)*log ((n:ℝ)+1)
    ‖F x y z-tensorFirstKind n₁ n₂ n₃ F x y z‖≤
      E₃+L n₃*E₂+L n₃*L n₂*E₁ := by sorry

end Liu
end
