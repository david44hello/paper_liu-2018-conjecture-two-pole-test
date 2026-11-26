import Liu.BergmanEvaluation

noncomputable section
open Set MeasureTheory Metric
open scoped ComplexConjugate
namespace Liu

def disc := Metric.ball (0:ℂ) 1

/-- Disc-to-upper-half-plane Cayley map sending zero to z. -/
def cayley (z w : ℂ) := (z-conj z*w)/(1-w)
def cayleyInv (z v : ℂ) := (v-z)/(v-conj z)
def cayleyJac (z w : ℂ) := (z-conj z)/(1-w)^2
def cayleyPull (z : ℂ) (F : ℂ → ℂ) (w : ℂ) := F (cayley z w)*cayleyJac z w

private theorem cayley_sep {z : ℂ} (hz : z ∈ upper) : z-conj z ≠ 0 := by
  intro he
  have h := congrArg Complex.im (sub_eq_zero.mp he)
  simp only [Complex.conj_im] at h
  change 0<z.im at hz; linarith

private theorem disc_ne_one {w : ℂ} (hw : w ∈ disc) : 1-w ≠ 0 := by
  intro he
  rw [←sub_eq_zero.mp he] at hw
  simpa [disc] using hw

private theorem reflected_distance_sq (v z : ℂ) :
    ‖v-conj z‖^2 = ‖v-z‖^2+4*v.im*z.im := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im]
  ring

theorem cayley_inv_right {z v : ℂ} (hz : z ∈ upper) (hv : v ∈ upper) :
    cayleyInv z v ∈ disc ∧ cayley z (cayleyInv z v) = v := by
  have hg := reflected_distance_sq v z
  have hi : 0 < v.im*z.im := mul_pos hv hz
  have hn : ‖v-z‖ < ‖v-conj z‖ := by nlinarith [norm_nonneg (v-z),norm_nonneg (v-conj z)]
  have hr := (norm_nonneg (v-z)).trans_lt hn
  have hd := norm_ne_zero_iff.mp hr.ne'
  have hd' := cayley_sep hz
  refine ⟨?_,?_⟩
  · change dist (cayleyInv z v) 0 < 1
    rw [dist_zero_right,cayleyInv,norm_div,div_lt_one hr]
    exact hn
  · have h : 1-cayleyInv z v = (z-conj z)/(v-conj z) := by
      unfold cayleyInv; field_simp [hd]; ring
    unfold cayley
    rw [h,cayleyInv]
    field_simp [hd,hd'] <;> ring

theorem cayley_inv_left {z w : ℂ} (hz : z ∈ upper) (hw : w ∈ disc) :
    cayley z w ∈ upper ∧ cayleyInv z (cayley z w) = w := by
  have hd := disc_ne_one hw
  have hn := cayley_sep hz
  have hsub : cayley z w - conj z = (z-conj z)/(1-w) := by
    unfold cayley; field_simp [hd]; ring
  have hsub' : cayley z w-z = w*((z-conj z)/(1-w)) := by
    unfold cayley; field_simp [hd]; ring
  have hpos := norm_pos_iff.mpr (div_ne_zero hn hd)
  have hnorm : ‖w‖ < 1 := by simpa [disc] using hw
  have hl : ‖cayley z w - z‖ < ‖cayley z w-conj z‖ := by
    rw [hsub,hsub',norm_mul]; simpa using mul_lt_mul_of_pos_right hnorm hpos
  have hs := reflected_distance_sq (cayley z w) z
  have hh := sq_lt_sq' (by linarith [norm_nonneg (cayley z w-z)]) hl
  constructor
  · change 0 < (cayley z w).im
    have hi : 0<(cayley z w).im*z.im := by linarith
    exact pos_of_mul_pos_left hi (le_of_lt hz)
  · rw [cayleyInv,hsub,hsub',mul_div_cancel_right₀ _ (div_ne_zero hn hd)]

theorem cayley_bijOn {z : ℂ} (hz : z ∈ upper) : BijOn (cayley z) disc upper := by
  refine ⟨fun _ hw => (cayley_inv_left hz hw).1,?_,?_⟩
  · intro x hx y hy h
    simpa only [(cayley_inv_left hz hx).2,(cayley_inv_left hz hy).2] using congrArg (cayleyInv z) h
  · intro v hv
    exact ⟨_,(cayley_inv_right hz hv).1,(cayley_inv_right hz hv).2⟩

theorem cayley_deriv (z : ℂ) {w : ℂ} (hw : w ∈ disc) : HasDerivAt (cayley z) (cayleyJac z w) w := by
  have hi := hasDerivAt_id w
  have h := ((hi.const_mul (conj z)).const_sub z).div (hi.const_sub 1) (disc_ne_one hw)
  convert h using 1
  · rfl
  · unfold cayleyJac
    simp [id]; ring

def cayleyRealDerivative (z w : ℂ) :=
  (ContinuousLinearMap.toSpanSingleton ℂ (cayleyJac z w)).restrictScalars ℝ

theorem cayley_det (z w : ℂ) :
    |(cayleyRealDerivative z w).det| = ‖cayleyJac z w‖^2 := by
  simp [cayleyRealDerivative,ContinuousLinearMap.det,LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq,Complex.normSq_eq_norm_sq]

theorem cayley_area_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : ℂ} (hz : z ∈ upper) (f : ℂ → E) :
    ∫ v in upper, f v ∂area = ∫ w in disc, ‖cayleyJac z w‖^2 • f (cayley z w) ∂area := by
  have hj := cayley_bijOn hz
  have hd (w : ℂ) (hw : w ∈ disc) : HasFDerivWithinAt (cayley z) (cayleyRealDerivative z w) disc w :=
    ((cayley_deriv z hw).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hh := integral_image_eq_integral_abs_det_fderiv_smul volume (s:=disc) Metric.isOpen_ball.measurableSet hd hj.injOn f
  rw [hj.image_eq] at hh
  simp_rw [cayley_det] at hh
  unfold area
  simp only [Measure.restrict_smul,integral_smul_measure,hh]

end Liu
