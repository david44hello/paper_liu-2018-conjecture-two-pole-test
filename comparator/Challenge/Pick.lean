import Mathlib

/- Frozen input: Liu/Pick.lean -/
noncomputable section
open scoped ComplexConjugate
open MeasureTheory Filter
namespace Liu

def upper : Set ℂ := {z | 0 < z.im}

def area : Measure ℂ := ENNReal.ofReal (1 / Real.pi) • volume

def k₀ : ℝ := Real.pi^2 / 12

structure Pair where
  a₁ : ℝ
  a₂ : ℝ
  w₁ : ℂ
  w₂ : ℂ
  ha₁ : 0 < a₁
  ha₂ : 0 < a₂
  hw₁ : w₁.im < 0
  hw₂ : w₂.im < 0

def pole (a : ℝ) (w z : ℂ) : ℂ := -(a:ℂ) / (z-w)

def Pair.value (p : Pair) (z : ℂ) : ℂ := pole p.a₁ p.w₁ z + pole p.a₂ p.w₂ z

def Pair.mass (p : Pair) : ℝ := p.a₁ + p.a₂

def normalMass (s : ℝ) : ℝ := 1 / (1 + Real.exp s)

def direction (γ : ℝ) : ℂ := Complex.exp (-(γ:ℂ) * Complex.I)

def normalSum (s γ u : ℝ) (z : ℂ) : ℂ :=
  pole (normalMass s) (-(u:ℂ)*Complex.I) z +
  pole (1-normalMass s) (-(u:ℂ)*Complex.I + direction γ) z

def source (S : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Complex.I/2) * (S z / conj (S z)) * conj (deriv S z)

def potential (S : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w in upper, (Real.log (‖z-conj w‖ / ‖z-w‖) : ℂ) * source S w ∂area

def field (S : ℂ → ℂ) (z : ℂ) : ℂ :=
  -((fderiv ℝ (potential S) z) 1 - Complex.I * (fderiv ℝ (potential S) z) Complex.I)

def halfDisc (R : ℝ) : Set ℂ := upper ∩ Metric.ball 0 R

def truncatedDeficit (S : ℂ → ℂ) (R : ℝ) : ℝ :=
  ∫ z in halfDisc R, k₀ * ‖S z‖^2 - ‖field S z‖^2 ∂area

def deficit (S : ℂ → ℂ) : ℝ := limUnder atTop (truncatedDeficit S)

def margin (s γ u : ℝ) : ℝ := deficit (normalSum s γ u) - k₀

def flux (s γ u : ℝ) : ℝ :=
  (∫ x : ℝ, ‖field (normalSum s γ u) x‖^2 - k₀ * ‖normalSum s γ u x‖^2) / Real.pi

end Liu
end
