module

public import Challenge.CutDomain
public import Challenge.PairedFlux
public import Challenge.ComplexTaylorFlux

@[expose] public section

/- Frozen input: Liu/AdmissibleContour.lean -/
noncomputable section
open Set MeasureTheory Real Complex Filter Metric
open scoped Topology
namespace Liu

structure RealContour where
  path : ℝ → ℂ
  ac : ∀ a b, AbsolutelyContinuousOnInterval path a b
  tail : ∃ R>0, ∀ x : ℝ, R≤|x| → path x=(x:ℂ)

def RealContour.admissible (γ : RealContour) (P Q : Fin 3 → ℂ) := ∀ x, γ.path x∈offCuts P Q

def RealContour.integral (γ : RealContour) (f : ℂ → ℂ) : ℂ := ∫ x : ℝ, f (γ.path x)*deriv γ.path x

structure WindowFamily (U : Set ℂ) where
  lower : Fin 3 → ℂ → ℂ
  partner : Fin 3 → ℂ → ℂ
  mass₁ : ℂ → ℂ
  mass₂ : ℂ → ℂ
  openSet : IsOpen U
  dl : ∀ i, DifferentiableOn ℂ (lower i) U
  dq : ∀ i, DifferentiableOn ℂ (partner i) U
  da : DifferentiableOn ℂ mass₁ U
  db : DifferentiableOn ℂ mass₂ U
  clear : ∀ w∈U, ∀ i j, ¬rayCollision (lower i w) (partner j w)

def WindowFamily.L {U} (W : WindowFamily U) (w : ℂ) := fun i => W.lower i w

def WindowFamily.Q {U} (W : WindowFamily U) (w : ℂ) := fun i => W.partner i w

def WindowFamily.H {U} (W : WindowFamily U) (w z : ℂ) := totalDensity (W.L w) (W.Q w) (W.mass₁ w) (W.mass₂ w) z

end Liu
end
