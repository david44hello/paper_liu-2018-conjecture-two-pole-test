import Challenge.Bergman

/- Frozen input: Liu/PickSums.lean -/
noncomputable section
open MeasureTheory Set
namespace Liu

structure PickSum (n : ℕ) where
  nonempty : 0 < n
  weight : Fin n → ℝ
  location : Fin n → ℂ
  pos : ∀ i, 0 < weight i
  below : ∀ i, (location i).im < 0

def PickSum.value {n : ℕ} (p : PickSum n) (z : ℂ) : ℂ := ∑ i, pole (p.weight i) (p.location i) z

def PickSum.mass {n : ℕ} (p : PickSum n) : ℝ := ∑ i, p.weight i

def poleBound (a : ℝ) (w : ℂ) : ℝ := a*(1 + (1+‖w‖)/(-w.im))

def PickSum.bound {n : ℕ} (p : PickSum n) : ℝ := ∑ i, poleBound (p.weight i) (p.location i)

def PickSum.power {n : ℕ} (p : PickSum n) (t : ℝ) (z : ℂ) : ℂ := (p.value z)^(t:ℂ)

end Liu
end
