module

public import Challenge.VerticalLog

@[expose] public section

/- Frozen input: Liu/LogTailKernel.lean -/
noncomputable section
open Set Real Complex
namespace Liu

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

def fieldCoefficient (lower : Bool) : ℂ := if lower then I/2 else -I/2

def tailSingle (s : Bool) (P Q : Fin 3 → ℂ) (i : Fin 2) (z : ℂ) : ℂ :=
  fieldCoefficient s * tailTerm s (P i.castSucc) (Q i.castSucc) z

def tailCross (s : Bool) (P Q : Fin 3 → ℂ) (a b z : ℂ) : ℂ :=
  fieldCoefficient s * (a*(tailTerm s (P 0) (Q 1) z-tailTerm s (P 0) (Q 2) z) +
    b*(tailTerm s (P 1) (Q 0) z-tailTerm s (P 1) (Q 2) z))

def tailSide (s : Bool) (P Q : Fin 3 → ℂ) (a b z : ℂ) : ℂ :=
  a*tailSingle s P Q 0 z+b*tailSingle s P Q 1 z+tailCross s P Q a b z

def tailPole (p z : ℂ) : ℂ := -(z-p)⁻¹

def subtractedTail (P Q : Fin 3 → ℂ) (a b z : ℂ) : ℂ :=
  let S := fun p => tailPole p z
  let H := fun i : Fin 2 => tailSingle true P Q i z*tailSingle false Q P i z -
    (k₀:ℂ)*S (P i.castSucc)*S (Q i.castSucc)
  tailSide true P Q a b z * tailSide false Q P a b z -
    (k₀:ℂ)*(a*S (P 0)+b*S (P 1))*(a*S (Q 0)+b*S (Q 1)) - a^2*H 0-b^2*H 1

end Liu
end
