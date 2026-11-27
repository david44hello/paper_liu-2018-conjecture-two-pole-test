module

public import Liu.FieldBound
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

@[expose] public section

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

/-- The factor in the observation derivative of the reflected logarithm.
The derivative in direction h is Re(h times this factor). -/
def greenResolvent (z w : ℂ) : ℂ := (z-conj w)⁻¹-(z-w)⁻¹

theorem greenResolvent_bound {z w : ℂ} (hz : 0≤z.im) (hw : w∈upper) (hne : z≠w) :
    ‖greenResolvent z w‖ ≤ 2*‖z-w‖⁻¹ := by
  have h := inv_anti₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) (distance_to_reflection_bound w z (le_of_lt hw) hz)
  apply (norm_sub_le ..).trans
  simp only [norm_inv]
  linarith

theorem greenResolvent_moment_bound {z w : ℂ} (hz : 0≤z.im) (hw : w∈upper) (hne : z≠w) :
    ‖greenResolvent z w‖ ≤ 2*w.im/‖z-w‖^2 := by
  have hcn : z≠conj w := fun e => by
    have h := congrArg Complex.im e; simp at h; change 0<w.im at hw; linarith
  have he : greenResolvent z w = (conj w-w)/((z-conj w)*(z-w)) := by
    unfold greenResolvent; field_simp [sub_ne_zero.mpr hne,sub_ne_zero.mpr hcn]; ring
  have hnorm : ‖conj w-w‖ = 2*w.im := by
    rw [norm_sub_rev,Complex.sub_conj,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) (le_of_lt hw))]
  rw [he,norm_div,hnorm,norm_mul]
  apply div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (le_of_lt hw)) (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
  rw [sq]
  exact mul_le_mul_of_nonneg_right (distance_to_reflection_bound w z (le_of_lt hw) hz) (norm_nonneg _)

private theorem log_norm_taylor {a h : ℂ} (ha : a≠0) (hh : ‖h‖≤‖a‖/2) :
    |log ‖a+h‖-log ‖a‖-(h/a).re| ≤ (‖h‖/‖a‖)^2 := by
  let u := h/a
  have hp := norm_pos_iff.mpr ha
  have hu : ‖u‖≤1/2 := by rw [show ‖u‖=‖h‖/‖a‖ from norm_div ..]; exact (div_le_iff₀ hp).mpr (by linarith)
  have hne : 1+u≠0 := fun e => by
    have he : u = -1 := by linear_combination e
    rw [he,norm_neg,norm_one] at hu; norm_num at hu
  have eqn : a+h=a*(1+u) := by dsimp [u]; field_simp [ha]
  rw [eqn,norm_mul,log_mul hp.ne' (norm_ne_zero_iff.mpr hne),add_sub_cancel_left]
  have hnorm : ‖u‖=‖h‖/‖a‖ := norm_div .. 
  change |log ‖1+u‖-u.re|≤_
  rw [←Complex.log_re,←Complex.sub_re,←hnorm]
  apply (Complex.abs_re_le_norm _).trans
  apply (Complex.norm_log_one_add_sub_self_le (by linarith : ‖u‖<1)).trans
  have hi := inv_anti₀ (by norm_num : (0:ℝ)<1/2) (by linarith : 1/2 ≤ 1-‖u‖)
  norm_num at hi
  nlinarith only [mul_le_mul_of_nonneg_left hi (sq_nonneg ‖u‖)]

theorem greenLog_remainder_near {z x w : ℂ} (hz : z∈upper) (hx : x∈upper) (hw : w∈upper)
    (hn : z≠w) (hn' : x≠w) :
    |greenLog x w-greenLog z w-((x-z)*greenResolvent z w).re| ≤
      ‖x-z‖*(‖x-w‖⁻¹+3*‖z-w‖⁻¹) := by
  have h := greenLog_difference hx hz hw hn' hn
  have hl := (Complex.abs_re_le_norm ((x-z)*greenResolvent z w)).trans_eq (norm_mul ..)
  have hd := hl.trans (mul_le_mul_of_nonneg_left (greenResolvent_bound (le_of_lt hz) hw hn) (norm_nonneg _))
  exact (abs_sub ..).trans (by linarith only [add_le_add h hd,show ‖x-z‖*(‖x-w‖⁻¹+‖z-w‖⁻¹)+‖x-z‖*(2*‖z-w‖⁻¹)=_ from
    (by ring : _=‖x-z‖*(‖x-w‖⁻¹+3*‖z-w‖⁻¹))])

theorem greenLog_remainder_far {z x w : ℂ} (hz : z∈upper) (hx : x∈upper) (hw : w∈upper)
    (hn : z≠w) (hn' : x≠w) (hsmall : ‖x-z‖≤‖z-w‖/2) :
    |greenLog x w-greenLog z w-((x-z)*greenResolvent z w).re| ≤ 2*(‖x-z‖/‖z-w‖)^2 := by
  have sep (v : ℂ) (hv : v∈upper) : v≠conj w := fun e => by
    have h := congrArg Complex.im e; simp at h; change 0<v.im at hv; change 0<w.im at hw; linarith
  have hcmp := distance_to_reflection_bound w z (le_of_lt hw) (le_of_lt hz)
  have h1 := log_norm_taylor (sub_ne_zero.mpr hn) hsmall
  have h2 := log_norm_taylor (sub_ne_zero.mpr (sep z hz)) (hsmall.trans (by linarith))
  rw [show z-w+(x-z)=x-w by ring] at h1
  rw [show z-conj w+(x-z)=x-conj w by ring] at h2
  have hq := div_le_div_of_nonneg_left (norm_nonneg (x-z)) (norm_pos_iff.mpr (sub_ne_zero.mpr hn)) hcmp
  have hq2 := pow_le_pow_left₀ (by positivity : 0≤‖x-z‖/‖z-conj w‖) hq 2
  have he : greenLog x w-greenLog z w-((x-z)*greenResolvent z w).re =
      (log ‖x-conj w‖-log ‖z-conj w‖-((x-z)/(z-conj w)).re)-
      (log ‖x-w‖-log ‖z-w‖-((x-z)/(z-w)).re) := by
    simp only [greenLog,greenResolvent,mul_sub,Complex.sub_re,
      log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (sep x hx))) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hn')),
      log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (sep z hz))) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hn))]
    simp only [div_eq_mul_inv]; ring
  rw [he]
  apply (abs_sub ..).trans
  linarith

end Liu
