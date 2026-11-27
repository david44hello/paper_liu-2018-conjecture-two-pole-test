module

public import Liu.Bergman

@[expose] public section

noncomputable section
open MeasureTheory Set
namespace Liu

/-- A finite, nonempty family allows repeated pole locations. -/
structure PickSum (n : ℕ) where
  nonempty : 0 < n
  weight : Fin n → ℝ
  location : Fin n → ℂ
  pos : ∀ i, 0 < weight i
  below : ∀ i, (location i).im < 0

def PickSum.value {n : ℕ} (p : PickSum n) (z : ℂ) : ℂ := ∑ i, pole (p.weight i) (p.location i) z
def PickSum.mass {n : ℕ} (p : PickSum n) : ℝ := ∑ i, p.weight i

theorem PickSum.value_im_pos {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0 ≤ z.im) :
    0 < (p.value z).im := by
  haveI : Nonempty (Fin n) := ⟨⟨0,p.nonempty⟩⟩
  simpa [PickSum.value,Complex.im_sum] using
    Finset.sum_pos (s := Finset.univ) (fun i _ => pole_im_pos (p.pos i) (p.below i) hz) Finset.univ_nonempty

theorem PickSum.holomorphic {n : ℕ} (p : PickSum n) : DifferentiableOn ℂ p.value upper := by
  intro z hz
  unfold PickSum.value
  apply DifferentiableWithinAt.fun_sum
  intro i _
  have h : z-p.location i ≠ 0 := sub_ne_zero.mpr (fun he => by
    have hh := congrArg Complex.im he
    have hw := p.below i
    change 0 < z.im at hz
    linarith)
  unfold pole
  fun_prop (disch := assumption)

def poleBound (a : ℝ) (w : ℂ) : ℝ := a*(1 + (1+‖w‖)/(-w.im))

theorem pole_global_decay {a : ℝ} {w z : ℂ} (ha : 0 < a) (hw : w.im < 0) (hz : 0 ≤ z.im) :
    ‖pole a w z‖ ≤ poleBound a w / (1+‖z‖) := by
  have hIm : -w.im ≤ ‖z-w‖ := calc
    -w.im ≤ (z-w).im := by simp; linarith
    _ ≤ ‖z-w‖ := Complex.im_le_norm _
  have hdepth : 0 < -w.im := by linarith
  have hn := hdepth.trans_le hIm
  have hz' : ‖z‖ ≤ ‖z-w‖ + ‖w‖ := by
    simpa using norm_add_le (z-w) w
  have hD : 0 ≤ (1+‖w‖)/(-w.im) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hIm hD
  have hid : (1+‖w‖)/(-w.im)*(-w.im)=1+‖w‖ := div_mul_cancel₀ _ hdepth.ne'
  have hbr : 1+‖z‖ ≤ (1+(1+‖w‖)/(-w.im))*‖z-w‖ := by nlinarith
  unfold pole poleBound
  rw [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,div_le_div_iff₀ hn (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hbr ha.le]

def PickSum.bound {n : ℕ} (p : PickSum n) : ℝ := ∑ i, poleBound (p.weight i) (p.location i)

theorem PickSum.bound_pos {n : ℕ} (p : PickSum n) : 0 < p.bound := by
  haveI : Nonempty (Fin n) := ⟨⟨0,p.nonempty⟩⟩
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro i _
  unfold poleBound
  have := p.pos i
  have hh := neg_pos.mpr (p.below i)
  positivity

theorem PickSum.global_decay {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖p.value z‖ ≤ p.bound/(1+‖z‖) := by
  unfold PickSum.value PickSum.bound
  rw [Finset.sum_div]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => pole_global_decay (p.pos i) (p.below i) hz)

def PickSum.power {n : ℕ} (p : PickSum n) (t : ℝ) (z : ℂ) : ℂ := (p.value z)^(t:ℂ)

theorem PickSum.power_measurable {n : ℕ} (p : PickSum n) (t : ℝ) : Measurable (p.power t) := by
  unfold PickSum.power PickSum.value pole
  fun_prop

theorem PickSum.power_memLp_two {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 1 < t) :
    MemLp (p.power t) 2 upperArea := by
  apply (memLp_two_iff_integrable_sq_norm (p.power_measurable t).aestronglyMeasurable).2
  have ht' : (Module.finrank ℝ ℂ:ℝ) < t*2 := by simp; linarith
  have hb := p.bound_pos
  have hnorm := integrable_one_add_norm (μ := (volume:Measure ℂ)) ht'
  have hdom : Integrable (fun z : ℂ => p.bound^(t*2) * (1+‖z‖)^(-(t*2))) upperArea :=
    (((hnorm.const_mul (p.bound^(t*2))).smul_measure ENNReal.ofReal_ne_top).restrict)
  refine hdom.mono' ((p.power_measurable t).norm.pow_const 2).aestronglyMeasurable ?_
  have hu : MeasurableSet upper := isOpen_lt continuous_const Complex.continuous_im |>.measurableSet
  apply (ae_restrict_iff' hu).2
  filter_upwards with z hz
  have hd := p.global_decay (le_of_lt hz)
  have hq : 0 < 1+‖z‖ := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  change ‖p.value z ^ (t:ℂ)‖^2 ≤ _
  rw [Complex.norm_cpow_real,←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _)]
  norm_num only [Nat.cast_ofNat]
  calc
    _ ≤ (p.bound/(1+‖z‖))^(t*2) := Real.rpow_le_rpow (norm_nonneg _) hd (by linarith)
    _ = _ := by rw [Real.div_rpow hb.le hq.le,Real.rpow_neg hq.le,div_eq_mul_inv]

end Liu
