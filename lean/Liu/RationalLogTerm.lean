import Liu.PolePolarization
import Liu.OnePoleBounds

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu

/-- The difference quotient of log(z-p) with base point q, including z=q. -/
def logChord (p q z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, (q+(t:ℂ)*(z-q)-p)⁻¹

def rationalLogTerm (p q z : ℂ) : ℂ :=
  (Complex.log (conj z-q)-Complex.log (p-q))/(z-p) - logChord p q z

theorem chord_im_bound {p q z : ℂ} (hq : 0≤q.im) (hz : 0≤z.im) {t : ℝ} (ht : t∈Icc 0 1) :
    -p.im ≤ (q+(t:ℂ)*(z-q)-p).im := by
  simp only [Complex.sub_im,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  nlinarith [mul_nonneg ht.1 hz,mul_nonneg (sub_nonneg.mpr ht.2) hq]

theorem logChord_eq {p q z : ℂ} (hp : p.im<0) (hq : 0<q.im) (hz : 0≤z.im) :
    logChord p q z = dslope (fun w => Complex.log (w-p)) q z := by
  by_cases he : z=q
  · subst z; rw [dslope_same]
    have hslit : q-p∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr (by simp; linarith : (q-p).im ≠ 0))
    have hd := ((hasDerivAt_id q).sub_const p).clog hslit
    change HasDerivAt (fun w : ℂ => Complex.log (w-p)) (1/(q-p)) q at hd
    rw [hd.deriv]; simp [logChord]
  · let A := fun t : ℝ => q+(t:ℂ)*(z-q)-p
    have hs (t : ℝ) (ht : t∈uIcc (0:ℝ) 1) : A t∈Complex.slitPlane := by
      rw [uIcc_of_le zero_le_one] at ht
      exact Complex.mem_slitPlane_iff.mpr (Or.inr ((neg_pos.mpr hp).trans_le (chord_im_bound hq.le hz ht)).ne')
    have hd (t : ℝ) (ht : t∈uIcc (0:ℝ) 1) :
        HasDerivAt (fun t => Complex.log (A t)) ((z-q)*(A t)⁻¹) t := by
      have H := ((((hasDerivAt_id (t:ℂ)).mul_const (z-q)).const_add q).sub_const p).clog (hs t ht)
      simpa [A,div_eq_mul_inv] using H.comp_ofReal
    have hcont : ContinuousOn (fun t : ℝ => (z-q)*(A t)⁻¹) (uIcc 0 1) := by
      intro t ht; have hn := Complex.slitPlane_ne_zero (hs t ht)
      dsimp [A] at hn ⊢; fun_prop (disch := assumption)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
    rw [intervalIntegral.integral_const_mul] at h
    simp only [A,Complex.ofReal_one,one_mul,add_sub_cancel,Complex.ofReal_zero,zero_mul,add_zero] at h
    rw [dslope_of_ne _ he,slope_def_field]
    exact (eq_div_iff (sub_ne_zero.mpr he)).mpr ((mul_comm ..).trans h)

/-- With q=conj c this is the expression of Appendix D, using the principal
logs on the upper half-plane and the true removable divided difference. -/
theorem rationalLogTerm_physical {p c z : ℂ} (hp : p.im<0) (hc : c.im<0) (hz : 0≤z.im) :
    rationalLogTerm p (conj c) z =
      (conj (Complex.log (z-c)) - conj (Complex.log (conj p-c)))/(z-p)
        - dslope (fun v => Complex.log (v-p)) (conj c) z := by
  have nz (w : ℂ) (hw : 0<w.im) : w.arg ≠ π := (upper_arg_range (z:=w) hw).2.ne
  have h₁ := Complex.log_conj (z-c) (nz _ (by simp; linarith))
  have h₂ := Complex.log_conj (conj p-c) (nz _ (by simp; linarith))
  simp only [map_sub,Complex.conj_conj] at h₁ h₂
  rw [rationalLogTerm,h₁,h₂,logChord_eq hp (by simpa using hc) hz]

end Liu
