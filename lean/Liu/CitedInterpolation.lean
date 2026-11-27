module

public import Liu.TensorInterpolation

@[expose] public section

noncomputable section
open Set Real Polynomial
namespace Liu

/-- H4 is a refereed external result, used as an explicit cited input. Ibrahimoglu, J. Inequal. Appl. 2016:93, §3.2
equation (13), gives the upper additive constant 0.9734… for n+1 roots.
Reindexing j by n-j preserves the Lebesgue function. The exact rational
upper constant below is rounded up. DOI 10.1186/s13660-016-1030-3. -/
def firstKindLebesgueInput : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ x : ℝ, x ∈ Set.Icc (-1:ℝ) 1 →
  let node := fun j : Fin (n+1) =>
    Real.cos ((2*(j:ℝ)+1)*Real.pi/(2*((n:ℝ)+1)))
  (∑ i : Fin (n+1), |(Lagrange.basis Finset.univ node i).eval x|) ≤
    (2/Real.pi)*Real.log ((n:ℝ)+1) + (974/1000:ℝ)

theorem cardinalSum_real (n : ℕ) (x : ℝ) :
    cardinalSum n x=∑ j : Fin (n+1), |(Lagrange.basis Finset.univ
      (fun i => cos (firstKindAngle n i)) j).eval x| := by
  unfold cardinalSum
  apply Finset.sum_congr rfl
  intro j _
  have h : Complex.ofReal ((Lagrange.basis Finset.univ (fun i => cos (firstKindAngle n i)) j).eval x) =
      (Lagrange.basis Finset.univ (firstKindNode n) j).eval (x:ℂ) := by
    simp [Lagrange.basis,Lagrange.basisDivisor,eval_prod,firstKindNode]
  rw [←h,Complex.norm_real,Real.norm_eq_abs]

theorem firstKind_lebesgue_bound_given (h4 : firstKindLebesgueInput) {n : ℕ} (hn : 1≤n)
    {x : ℝ} (hx : x∈Icc (-1:ℝ) 1) : cardinalSum n x≤1+(2/π)*log ((n:ℝ)+1) := by
  rw [cardinalSum_real]
  apply (h4 n hn x hx).trans
  linarith

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
      E₃+L n₃*E₂+L n₃*L n₂*E₁ := by
  have hLeb₂ := firstKind_lebesgue_bound_given h4 hn₂ hy
  have hLeb₃ := firstKind_lebesgue_bound_given h4 hn₃ hz
  have hEllipse (r : ℝ) (hr : 1<r) : (0:ℂ)∈bernsteinEllipse r := by
    change ‖(0:ℂ)-1‖+‖(0:ℂ)+1‖≤r+r⁻¹
    simp only [zero_sub,norm_neg,norm_one,zero_add]
    have hp := zero_lt_one.trans hr
    rw [←one_div]
    field_simp [hp.ne']
    nlinarith [sq_nonneg (r-1)]
  have hunit : (0:ℝ)∈Icc (-1:ℝ) 1 := by constructor <;> norm_num
  have hM₁ := (norm_nonneg _).trans ((first 0 hunit 0).2 0 (hEllipse _ h₁))
  have hM₂ := (norm_nonneg _).trans ((middle 0 hunit 0).2 0 (hEllipse _ h₂))
  have hcard (n : ℕ) (x : ℝ) : 0≤cardinalSum n x := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hpos₁ : 0<r₁ := zero_lt_one.trans h₁
  have hpos₂ : 0<r₂ := zero_lt_one.trans h₂
  have hr₁ := sub_pos.mpr h₁
  have hr₂ := sub_pos.mpr h₂
  apply (firstKind_tensor_error n₁ n₂ n₃ h₁ h₂ h₃ last middle first hx hy hz).trans
  dsimp only
  have H₂ := mul_le_mul_of_nonneg_right hLeb₃ (by positivity : 0≤4*M₂/(r₂^n₂*(r₂-1)))
  have H₁ := mul_le_mul_of_nonneg_right (mul_le_mul hLeb₃ hLeb₂ (hcard _ _) ((hcard _ _).trans hLeb₃))
    (by positivity : 0≤4*M₁/(r₁^n₁*(r₁-1)))
  linarith only [H₁,H₂]

end Liu
