module

public import Mathlib

@[expose] public section

/-! Concrete two-pole functions and the normalized half-plane Green potential. -/
noncomputable section
open scoped ComplexConjugate
open MeasureTheory Filter
namespace Liu
scoped instance instAtLeastTwo2 : Nat.AtLeastTwo 2 := ⟨Nat.le_refl 2⟩


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

theorem Pair.mass_pos (p : Pair) : 0 < p.mass := add_pos p.ha₁ p.ha₂

theorem pole_im_pos {a : ℝ} {w z : ℂ} (ha : 0 < a) (hw : w.im < 0) (hz : 0 ≤ z.im) :
    0 < (pole a w z).im := by
  have hd : z-w ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hn := Complex.normSq_pos.mpr hd
  simp [pole, Complex.div_im, Complex.sub_im, Complex.sub_re]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos ha (sub_pos.mpr (hw.trans_le hz)))) hn

theorem Pair.im_pos (p : Pair) {z : ℂ} (hz : 0 ≤ z.im) : 0 < (p.value z).im :=
  add_pos (pole_im_pos p.ha₁ p.hw₁ hz) (pole_im_pos p.ha₂ p.hw₂ hz)

theorem Pair.value_ne_zero (p : Pair) {z : ℂ} (hz : 0 ≤ z.im) : p.value z ≠ 0 := by
  intro he
  have h := p.im_pos hz
  simp [he] at h

theorem Pair.holomorphic (p : Pair) : DifferentiableOn ℂ p.value upper := by
  intro z hz
  have h1 : z-p.w₁ ≠ 0 := sub_ne_zero.mpr fun h => by
    have := congrArg Complex.im h
    have hw := p.hw₁
    change 0 < z.im at hz
    linarith
  have h2 : z-p.w₂ ≠ 0 := sub_ne_zero.mpr fun h => by
    have := congrArg Complex.im h
    have hw := p.hw₂
    change 0 < z.im at hz
    linarith
  unfold Pair.value pole
  fun_prop (disch := assumption)

def normalMass (s : ℝ) : ℝ := 1 / (1 + Real.exp s)

def direction (γ : ℝ) : ℂ := Complex.exp (-(γ:ℂ) * Complex.I)

def normalSum (s γ u : ℝ) (z : ℂ) : ℂ :=
  pole (normalMass s) (-(u:ℂ)*Complex.I) z +
  pole (1-normalMass s) (-(u:ℂ)*Complex.I + direction γ) z

def source (S : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Complex.I/2) * (S z / conj (S z)) * conj (deriv S z)

/-- With area dx dy / π and -ΔU=2ρ, the Green integral has no additional scalar. -/
def potential (S : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w in upper, (Real.log (‖z-conj w‖ / ‖z-w‖) : ℂ) * source S w ∂area

def field (S : ℂ → ℂ) (z : ℂ) : ℂ :=
  -((fderiv ℝ (potential S) z) 1 - Complex.I * (fderiv ℝ (potential S) z) Complex.I)

def halfDisc (R : ℝ) : Set ℂ := upper ∩ Metric.ball 0 R

def truncatedDeficit (S : ℂ → ℂ) (R : ℝ) : ℝ :=
  ∫ z in halfDisc R, k₀ * ‖S z‖^2 - ‖field S z‖^2 ∂area

/-- The intended finite part comes with a separate convergence obligation. -/
def deficit (S : ℂ → ℂ) : ℝ := limUnder atTop (truncatedDeficit S)

def margin (s γ u : ℝ) : ℝ := deficit (normalSum s γ u) - k₀

def flux (s γ u : ℝ) : ℝ :=
  (∫ x : ℝ, ‖field (normalSum s γ u) x‖^2 - k₀ * ‖normalSum s γ u x‖^2) / Real.pi

end Liu
