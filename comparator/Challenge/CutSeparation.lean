import Challenge.LogTailKernel

/- Frozen input: Liu/CutSeparation.lean -/
noncomputable section
open Set Real Complex
open scoped ComplexConjugate
namespace Liu

def rayCollision (p q : ℂ) := p.re=q.re ∧ q.im ≤ p.im

def stripMass (s : ℂ) := (1+Complex.exp s)⁻¹

def windowLower (a : ℂ) (γ u : ℝ) : Fin 3 → ℂ :=
  ![-(u:ℂ)*I,-(u:ℂ)*I+direction γ,-(u:ℂ)*I+a*direction γ]

def windowUpper (a : ℂ) (γ u : ℝ) : Fin 3 → ℂ :=
  ![(u:ℂ)*I,(u:ℂ)*I+conj (direction γ),(u:ℂ)*I+a*conj (direction γ)]

theorem strip_no_collision {s : ℂ} (hs : |s.im| < π/2) {γ u : ℝ}
    (hg : γ∈Icc 0 (π/2)) (hu : 0 < u) (i j : Fin 3) :
    ¬rayCollision (windowLower (stripMass s) γ u i) (windowUpper (stripMass s) γ u j) := by sorry

end Liu
end
