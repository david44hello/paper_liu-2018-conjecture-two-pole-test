module

public import Liu.Cover
public import Liu.ExpBounds
public import Liu.Pick

@[expose] public section

noncomputable section
namespace Liu.Certificate

def Box.maxMassLog (b : Box) : ℚ := max b.cell.sHi (-b.cell.sLo)
def Box.muMin (b : Box) : ℝ := 1/(1 + Real.exp b.maxMassLog)
def Box.aMin (b : Box) : ℝ := normalMass b.cell.sHi

def Box.generalBeta (b : Box) : ℝ :=
  2^34 / b.muMin^2 * b.depth * (2 + Real.log (1/b.depth))

def Box.mixedBeta (b : Box) : ℝ :=
  let sn := Real.sin (b.chart.angle b.yLo)
  b.depth * (64/sn^4 * (1+Real.log (1/b.depth)) + 4096/(b.aMin^2 * sn^8))

def Box.beta (b : Box) : ℝ :=
  if (53/100:ℝ) ≤ b.chart.angle b.yLo then min b.generalBeta b.mixedBeta else b.generalBeta

/-- The exact logarithm of the threshold is the base exponent minus the number of low pieces. -/
theorem Box.log_inv_depth (b : Box) : Real.log (1/b.depth) = -(b.logDepth:ℝ) := by
  simp [Box.depth,one_div,Real.log_inv]

def Box.nHalfSteps (b : Box) : ℕ :=
  (if b.chart = .largeAngle then 27 else 19) + 2*b.cell.pieces

theorem Box.logDepth_eq (b : Box) : (b.logDepth : ℝ) = (b.nHalfSteps:ℝ)*(-(1/2:ℝ)) := by
  unfold Box.logDepth Box.nHalfSteps
  split <;> push_cast <;> ring

/-- A fixed rational majorant for e^(-1/2), raised to the indicated number of half steps. -/
def Box.depthUpper (b : Box) : ℚ := (606530660/1000000000)^b.nHalfSteps

theorem Box.depth_le_upper (b : Box) : b.depth ≤ (b.depthUpper:ℝ) := by
  unfold Box.depth Box.depthUpper
  rw [b.logDepth_eq,Real.exp_nat_mul]
  push_cast
  exact pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_half_upper _

/-- Rational majorant for the general small-depth formula. -/
def Box.generalMajor (b : Box) : ℚ :=
  2^34 * (1 + expUpper b.maxMassLog)^2 * b.depthUpper * (2 - b.logDepth)

def Box.sinLower (b : Box) : ℚ := if b.yLo = 1 then 841/1000 else 5054/10000

def Box.mixedMajor (b : Box) : ℚ :=
  b.depthUpper * (64/b.sinLower^4 * (1-b.logDepth) +
    4096 * (1+expUpper b.cell.sHi)^2 / b.sinLower^8)

def Box.betaMajor (b : Box) : ℚ :=
  if b.chart = .largeAngle then min b.generalMajor b.mixedMajor else b.generalMajor

theorem Box.logDepth_nonpos (b : Box) : (b.logDepth:ℝ) ≤ 0 := by
  rw [b.logDepth_eq]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by norm_num)

theorem Box.general_le_major (b : Box) (hq : |b.maxMassLog| ≤ 16) :
    b.generalBeta ≤ (b.generalMajor:ℝ) := by
  have hexp := expUpper_sound b.maxMassLog hq
  have h₁ : 0 ≤ 2 - (b.logDepth:ℝ) := by linarith [b.logDepth_nonpos]
  have hfac : 2^34 / b.muMin^2 = 2^34 * (1+Real.exp (b.maxMassLog:ℝ))^2 := by
    simp [Box.muMin,div_pow,div_eq_mul_inv]
  unfold Box.generalBeta Box.generalMajor
  rw [hfac,b.log_inv_depth]
  push_cast
  rw [← sub_eq_add_neg]
  gcongr <;> first | exact b.depth_pos.le | exact b.depth_le_upper | positivity | assumption | linarith

private theorem sin_lower_large (b : Box) (hc : b.chart = .largeAngle)
    (hy : b.yLo = 53/100 ∨ b.yLo = 1) :
    0 < (b.sinLower:ℝ) ∧ (b.sinLower:ℝ) ≤ Real.sin (b.chart.angle b.yLo) := by
  rcases hy with hy|hy
  · simp [Box.sinLower,hy,hc,Chart.angle]
    norm_num at * <;> linarith [sin_053_lower]
  · simp [Box.sinLower,hy,hc,Chart.angle]
    norm_num at * <;> linarith [sin_one_lower]

theorem Box.mixed_le_major (b : Box) (hc : b.chart = .largeAngle)
    (hy : b.yLo = 53/100 ∨ b.yLo = 1) (hq : |b.cell.sHi| ≤ 16) :
    b.mixedBeta ≤ (b.mixedMajor:ℝ) := by
  obtain ⟨hpos,hsin⟩ := sin_lower_large b hc hy
  have hexp := expUpper_sound b.cell.sHi hq
  have h₁ : 0 ≤ 1 - (b.logDepth:ℝ) := by linarith [b.logDepth_nonpos]
  have hspos := hpos.trans_le hsin
  have hdup := b.depth_pos.trans_le b.depth_le_upper
  have hepos := Real.exp_pos (b.cell.sHi:ℝ)
  have hem := hepos.trans_le hexp
  have hfac : 4096 / (b.aMin^2 * (Real.sin (b.chart.angle b.yLo))^8) =
      4096 * (1+Real.exp (b.cell.sHi:ℝ))^2 / (Real.sin (b.chart.angle b.yLo))^8 := by
    simp [Box.aMin,normalMass,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
  simp only [Box.mixedBeta,Box.mixedMajor]
  rw [hfac,b.log_inv_depth,← sub_eq_add_neg]
  push_cast
  gcongr <;> first | exact b.depth_pos.le | exact b.depth_le_upper | positivity | assumption | linarith

theorem Box.beta_le_major (b : Box) (hm : |b.maxMassLog| ≤ 16) (hs : |b.cell.sHi| ≤ 16)
    (hy : b.chart = .largeAngle → b.yLo = 53/100 ∨ b.yLo = 1) :
    b.beta ≤ (b.betaMajor:ℝ) := by
  by_cases hc : b.chart = .largeAngle
  · have hyg := hy hc
    have h : (53/100:ℝ) ≤ b.chart.angle b.yLo := by
      rcases hyg with h|h <;> norm_num [h,hc,Chart.angle]
    simp only [Box.beta, if_pos h, Box.betaMajor, if_pos hc, Rat.cast_min]
    exact min_le_min (b.general_le_major hm) (b.mixed_le_major hc hyg hs)
  · simp only [Box.betaMajor, if_neg hc]
    unfold Box.beta
    split
    · exact (min_le_left _ _).trans (b.general_le_major hm)
    · exact b.general_le_major hm

end Liu.Certificate
