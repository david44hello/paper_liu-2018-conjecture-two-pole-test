-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
module

public import Mathlib

@[expose] public section

/-!
# Two-pole test of the Liu (2018) conjecture on the norm of the Bergman projection

Theorems 1.1 and 3.5 establish the strict deficit and negative slope (hence strict quotient
inequality below pi^2/12 for sufficiently small positive exponent increments) for every two-pole
Pick function, assuming the computer-checked bounds of Proposition 6.1 over 168 fixed boxes as
one explicit hypothesis (`Certificate.boxBounds`). Proposition 6.1 is checked by computer outside
Lean. The full Liu (2018) conjecture remains open.
-/

noncomputable section
open Set Real MeasureTheory Filter
open scoped ComplexConjugate Topology

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

def upperArea : Measure ℂ := area.restrict upper
abbrev PlaneL2 := Lp ℂ 2 upperArea

/-- Vectors represented by square-integrable holomorphic functions in the upper half-plane. -/
def analyticVectors : Set PlaneL2 :=
  {x | ∃ (f : ℂ → ℂ) (h : MemLp f 2 upperArea), DifferentiableOn ℂ f upper ∧ x = h.toLp f}

/-- Taking closed span constructs the orthogonal projection without assuming the density
or closed-representative theorem. The latter identification is a separate analytic obligation. -/
def analyticSubspace : Submodule ℂ PlaneL2 := (Submodule.span ℂ analyticVectors).topologicalClosure

def project : PlaneL2 →L[ℂ] PlaneL2 := (Submodule.span ℂ analyticVectors).topologicalClosure.starProjection

def asL2 (f : ℂ → ℂ) : PlaneL2 := by
  classical
  exact if h : MemLp f 2 upperArea then h.toLp f else 0

def logInput (f : ℂ → ℂ) (z : ℂ) : ℂ := f z * (Real.log ‖f z‖ : ℂ)

def quotient (f : ℂ → ℂ) : ℝ :=
  let input := asL2 (logInput f)
  ‖input - project input‖^2 / ‖asL2 f‖^2

def critical (p : Pair) (ε : ℝ) (z : ℂ) : ℂ := (p.value z) ^ ((1+ε:ℝ):ℂ)

def Pair.slope (p : Pair) : ℝ := 2*(k₀-deficit p.value / p.mass^2)

def Pair.quotientDomain (p : Pair) (ε : ℝ) : Prop :=
  MemLp (critical p ε) 2 upperArea ∧ MemLp (logInput (critical p ε)) 2 upperArea ∧
    0 < ‖asL2 (critical p ε)‖

namespace Certificate

inductive Chart where
  | corner | logAngle | largeAngle
  deriving DecidableEq, Repr

structure Cell where
  sLo : ℚ
  sHi : ℚ
  pieces : ℕ
  /-- Integer in millionths printed for the lower endpoint after all low pieces. -/
  displayMicro : ℕ
  deriving DecidableEq, Repr

structure Band where
  chart : Chart
  yLo : ℚ
  yHi : ℚ
  cells : List Cell
  deriving DecidableEq, Repr

structure Box where
  chart : Chart
  yLo : ℚ
  yHi : ℚ
  cell : Cell
  deriving DecidableEq, Repr

def Band.box (r : Band) (c : Cell) : Box := ⟨r.chart, r.yLo, r.yHi, c⟩

noncomputable def Chart.angle (chart : Chart) (q : ℚ) : ℝ :=
  if chart = .logAngle then Real.exp q else q

def Box.contains (b : Box) (s γ : ℝ) : Prop :=
  b.cell.sLo ≤ s ∧ s ≤ b.cell.sHi ∧ b.chart.angle b.yLo ≤ γ ∧ γ ≤ b.chart.angle b.yHi

def Box.logDepth (b : Box) : ℚ :=
  (if b.chart = .largeAngle then -(27 / 2) else -(19 / 2)) - b.cell.pieces

noncomputable def Box.depth (b : Box) : ℝ := Real.exp b.logDepth

def Box.safeLower (b : Box) : ℚ := ((b.cell.displayMicro : ℚ) - 1) / 1000000

theorem Box.depth_pos (b : Box) : 0 < b.depth := Real.exp_pos _

def cornerBands : List Band := [
  ⟨.corner, 0, 1 / 1048576, [
    ⟨-25 / 3, -175 / 27, 43, 70958⟩,
    ⟨-175 / 27, -125 / 27, 39, 68035⟩,
    ⟨-125 / 27, -25 / 9, 35, 57658⟩,
    ⟨-25 / 9, -25 / 27, 32, 35972⟩,
    ⟨-25 / 27, 25 / 27, 28, 28945⟩,
    ⟨25 / 27, 25 / 9, 32, 35794⟩,
    ⟨25 / 9, 125 / 27, 35, 57738⟩,
    ⟨125 / 27, 175 / 27, 39, 67159⟩,
    ⟨175 / 27, 25 / 3, 43, 70595⟩]⟩]

def logBands : List Band := [
  ⟨.logAngle, -1483 / 100, -1373 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 70519⟩,
    ⟨-175 / 27, -125 / 27, 39, 67580⟩,
    ⟨-125 / 27, -25 / 9, 35, 57763⟩,
    ⟨-25 / 9, -25 / 27, 32, 36262⟩,
    ⟨-25 / 27, 25 / 27, 28, 29316⟩,
    ⟨25 / 27, 25 / 9, 32, 36068⟩,
    ⟨25 / 9, 125 / 27, 35, 57829⟩,
    ⟨125 / 27, 175 / 27, 39, 67200⟩,
    ⟨175 / 27, 25 / 3, 43, 70627⟩]⟩,
  ⟨.logAngle, -1373 / 100, -1263 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 70556⟩,
    ⟨-175 / 27, -125 / 27, 39, 67278⟩,
    ⟨-125 / 27, -25 / 9, 35, 57492⟩,
    ⟨-25 / 9, -25 / 27, 32, 36533⟩,
    ⟨-25 / 27, 25 / 27, 28, 29625⟩,
    ⟨25 / 27, 25 / 9, 32, 36292⟩,
    ⟨25 / 9, 125 / 27, 35, 57903⟩,
    ⟨125 / 27, 175 / 27, 39, 67231⟩,
    ⟨175 / 27, 25 / 3, 43, 70650⟩]⟩,
  ⟨.logAngle, -1263 / 100, -1153 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 70616⟩,
    ⟨-175 / 27, -125 / 27, 39, 67454⟩,
    ⟨-125 / 27, -25 / 9, 35, 57854⟩,
    ⟨-25 / 9, -25 / 27, 32, 37109⟩,
    ⟨-25 / 27, 25 / 27, 28, 30259⟩,
    ⟨25 / 27, 25 / 9, 32, 36745⟩,
    ⟨25 / 9, 125 / 27, 35, 58050⟩,
    ⟨125 / 27, 175 / 27, 39, 67292⟩,
    ⟨175 / 27, 25 / 3, 43, 70696⟩]⟩,
  ⟨.logAngle, -1153 / 100, -1043 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 70750⟩,
    ⟨-175 / 27, -125 / 27, 39, 67617⟩,
    ⟨-125 / 27, -25 / 9, 35, 57500⟩,
    ⟨-25 / 9, -25 / 27, 32, 37401⟩,
    ⟨-25 / 27, 25 / 27, 28, 31392⟩,
    ⟨25 / 27, 25 / 9, 32, 37536⟩,
    ⟨25 / 9, 125 / 27, 35, 58300⟩,
    ⟨125 / 27, 175 / 27, 39, 67392⟩,
    ⟨175 / 27, 25 / 3, 43, 70768⟩]⟩,
  ⟨.logAngle, -1043 / 100, -933 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 70076⟩,
    ⟨-175 / 27, -125 / 27, 39, 67762⟩,
    ⟨-125 / 27, -25 / 9, 35, 58129⟩,
    ⟨-25 / 9, -25 / 27, 32, 38748⟩,
    ⟨-25 / 27, 25 / 27, 28, 32012⟩,
    ⟨25 / 27, 25 / 9, 32, 38653⟩,
    ⟨25 / 9, 125 / 27, 35, 58635⟩,
    ⟨125 / 27, 175 / 27, 39, 67515⟩,
    ⟨175 / 27, 25 / 3, 43, 70638⟩]⟩,
  ⟨.logAngle, -933 / 100, -823 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 70497⟩,
    ⟨-175 / 27, -125 / 27, 39, 67925⟩,
    ⟨-125 / 27, -25 / 9, 35, 58796⟩,
    ⟨-25 / 9, -25 / 27, 32, 39907⟩,
    ⟨-25 / 27, 25 / 27, 28, 33782⟩,
    ⟨25 / 27, 25 / 9, 32, 39181⟩,
    ⟨25 / 9, 125 / 27, 35, 58630⟩,
    ⟨125 / 27, 175 / 27, 39, 67338⟩,
    ⟨175 / 27, 25 / 3, 43, 70626⟩]⟩,
  ⟨.logAngle, -823 / 100, -713 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 71562⟩,
    ⟨-175 / 27, -125 / 27, 39, 68075⟩,
    ⟨-125 / 27, -25 / 9, 35, 58912⟩,
    ⟨-25 / 9, -25 / 27, 32, 40577⟩,
    ⟨-25 / 27, 25 / 27, 28, 34729⟩,
    ⟨25 / 27, 25 / 9, 32, 40285⟩,
    ⟨25 / 9, 125 / 27, 35, 59138⟩,
    ⟨125 / 27, 175 / 27, 39, 67341⟩,
    ⟨175 / 27, 25 / 3, 43, 70320⟩]⟩,
  ⟨.logAngle, -713 / 100, -603 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 71092⟩,
    ⟨-175 / 27, -125 / 27, 39, 67795⟩,
    ⟨-125 / 27, -25 / 9, 35, 59400⟩,
    ⟨-25 / 9, -25 / 27, 32, 41296⟩,
    ⟨-25 / 27, 25 / 27, 28, 35167⟩,
    ⟨25 / 27, 25 / 9, 32, 40425⟩,
    ⟨25 / 9, 125 / 27, 35, 58690⟩,
    ⟨125 / 27, 175 / 27, 39, 67325⟩,
    ⟨175 / 27, 25 / 3, 43, 70432⟩]⟩,
  ⟨.logAngle, -603 / 100, -493 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 71395⟩,
    ⟨-175 / 27, -125 / 27, 39, 68681⟩,
    ⟨-125 / 27, -25 / 9, 35, 60315⟩,
    ⟨-25 / 9, -25 / 27, 32, 42545⟩,
    ⟨-25 / 27, 25 / 27, 28, 36547⟩,
    ⟨25 / 27, 25 / 9, 32, 41951⟩,
    ⟨25 / 9, 125 / 27, 35, 58499⟩,
    ⟨125 / 27, 175 / 27, 39, 67571⟩,
    ⟨175 / 27, 25 / 3, 43, 69779⟩]⟩,
  ⟨.logAngle, -493 / 100, -383 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 70774⟩,
    ⟨-175 / 27, -125 / 27, 39, 68678⟩,
    ⟨-125 / 27, -25 / 9, 35, 61234⟩,
    ⟨-25 / 9, -25 / 27, 32, 44871⟩,
    ⟨-25 / 27, 25 / 27, 28, 39517⟩,
    ⟨25 / 27, 25 / 9, 32, 42897⟩,
    ⟨25 / 9, 125 / 27, 35, 59643⟩,
    ⟨125 / 27, 175 / 27, 39, 68104⟩,
    ⟨175 / 27, 25 / 3, 43, 69678⟩]⟩,
  ⟨.logAngle, -383 / 100, -273 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 70302⟩,
    ⟨-175 / 27, -125 / 27, 39, 68938⟩,
    ⟨-125 / 27, -25 / 9, 35, 63781⟩,
    ⟨-25 / 9, -25 / 27, 32, 49035⟩,
    ⟨-25 / 27, 25 / 27, 28, 43713⟩,
    ⟨25 / 27, 25 / 9, 32, 47820⟩,
    ⟨25 / 9, 125 / 27, 35, 59721⟩,
    ⟨125 / 27, 175 / 27, 39, 69102⟩,
    ⟨175 / 27, 25 / 3, 43, 69818⟩]⟩,
  ⟨.logAngle, -273 / 100, -163 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 69462⟩,
    ⟨-175 / 27, -125 / 27, 39, 68366⟩,
    ⟨-125 / 27, -25 / 9, 35, 61297⟩,
    ⟨-25 / 9, -25 / 27, 32, 51037⟩,
    ⟨-25 / 27, 25 / 27, 28, 49907⟩,
    ⟨25 / 27, 25 / 9, 32, 53580⟩,
    ⟨25 / 9, 125 / 27, 35, 61592⟩,
    ⟨125 / 27, 175 / 27, 39, 67996⟩,
    ⟨175 / 27, 25 / 3, 43, 70243⟩]⟩,
  ⟨.logAngle, -163 / 100, -63 / 100, [
    ⟨-25 / 3, -175 / 27, 43, 66544⟩,
    ⟨-175 / 27, -125 / 27, 39, 65283⟩,
    ⟨-125 / 27, -25 / 9, 35, 57615⟩,
    ⟨-25 / 9, -25 / 27, 32, 39114⟩,
    ⟨-25 / 27, 25 / 27, 28, 31365⟩,
    ⟨25 / 27, 25 / 9, 32, 51536⟩,
    ⟨25 / 9, 125 / 27, 35, 56884⟩,
    ⟨125 / 27, 175 / 27, 39, 67376⟩,
    ⟨175 / 27, 25 / 3, 43, 70215⟩]⟩]

def largeBands : List Band := [
  ⟨.largeAngle, 53 / 100, 1, [
    ⟨-25 / 3, -23 / 3, 8, 68999⟩,
    ⟨-23 / 3, -7, 8, 68915⟩,
    ⟨-7, -19 / 3, 8, 68751⟩,
    ⟨-19 / 3, -17 / 3, 8, 68495⟩,
    ⟨-17 / 3, -5, 8, 67782⟩,
    ⟨-5, -13 / 3, 8, 66684⟩,
    ⟨-13 / 3, -11 / 3, 8, 64113⟩,
    ⟨-11 / 3, -3, 8, 60702⟩,
    ⟨-3, -7 / 3, 9, 55377⟩,
    ⟨-7 / 3, -5 / 3, 9, 48833⟩,
    ⟨-5 / 3, -1, 9, 43441⟩,
    ⟨-1, -1 / 3, 9, 41082⟩,
    ⟨-1 / 3, 1 / 3, 10, 42824⟩,
    ⟨1 / 3, 1, 11, 47592⟩,
    ⟨1, 5 / 3, 12, 57740⟩,
    ⟨5 / 3, 7 / 3, 13, 63013⟩,
    ⟨7 / 3, 3, 14, 66636⟩,
    ⟨3, 11 / 3, 16, 68193⟩,
    ⟨11 / 3, 13 / 3, 17, 68968⟩,
    ⟨13 / 3, 5, 18, 68413⟩,
    ⟨5, 17 / 3, 20, 67365⟩,
    ⟨17 / 3, 19 / 3, 21, 68664⟩,
    ⟨19 / 3, 7, 22, 68897⟩,
    ⟨7, 23 / 3, 24, 69135⟩,
    ⟨23 / 3, 25 / 3, 25, 68729⟩]⟩,
  ⟨.largeAngle, 1, 1571 / 1000, [
    ⟨-25 / 3, -125 / 17, 4, 68638⟩,
    ⟨-125 / 17, -325 / 51, 4, 68412⟩,
    ⟨-325 / 51, -275 / 51, 4, 67565⟩,
    ⟨-275 / 51, -75 / 17, 4, 66076⟩,
    ⟨-75 / 17, -175 / 51, 4, 63040⟩,
    ⟨-175 / 51, -125 / 51, 5, 56450⟩,
    ⟨-125 / 51, -25 / 17, 5, 45650⟩,
    ⟨-25 / 17, -25 / 51, 5, 39336⟩,
    ⟨-25 / 51, 25 / 51, 6, 39422⟩,
    ⟨25 / 51, 25 / 17, 8, 44758⟩,
    ⟨25 / 17, 125 / 51, 9, 57883⟩,
    ⟨125 / 51, 175 / 51, 11, 65332⟩,
    ⟨175 / 51, 75 / 17, 13, 67528⟩,
    ⟨75 / 17, 275 / 51, 15, 67929⟩,
    ⟨275 / 51, 325 / 51, 17, 69280⟩,
    ⟨325 / 51, 125 / 17, 19, 68902⟩,
    ⟨125 / 17, 25 / 3, 21, 69566⟩]⟩]

def bands : List Band := cornerBands ++ logBands ++ largeBands
def boxes : List Box := bands.flatMap fun r => r.cells.map r.box

/-- Proposition 6.1 with the fixed 168 depth / lower-bound pairs of the certificate. -/
def boxBounds : Prop :=
  ∀ b ∈ boxes, ∀ s γ : ℝ, b.contains s γ → γ ≤ Real.pi/2 →
    (∀ u : ℝ, b.depth ≤ u → 0 < margin s γ u) ∧
      (b.safeLower:ℝ) ≤ margin s γ b.depth

end Certificate

/-- Theorem 3.5 with the two clauses of the fixed computer certificate as its
only external premise. This applies to unequal and coincident lower poles. -/
theorem pair_deficit_of_certificate (p : Pair) (box : Certificate.boxBounds) :
    k₀*p.mass^2<deficit p.value := by sorry

/-- Theorem 1.1 with the fixed computer certificate as its sole premise. -/
theorem two_pole_test_of_certificate (p : Pair) (box : Certificate.boxBounds) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2<deficit p.value ∧ p.slope<0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0<ε → ε<ε₀ → p.quotientDomain ε ∧ quotient (critical p ε)<k₀ := by sorry

end Liu
