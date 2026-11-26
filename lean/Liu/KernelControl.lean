import Liu.KernelWeight
import Liu.LogOscillation

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

theorem PickSum.log_power_growth {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0 < t) :
    ∃ B > 0, ∀ w : ℂ, 0 ≤ w.im →
      |log ‖p.power t w‖| ≤ B+t*log (1+‖w‖) ∧
      t*log (1+‖w‖) ≤ B+|log ‖p.power t w‖| := by
  obtain ⟨c,hc,hscale⟩ := p.power_two_sided ht.le
  let D := p.bound^t
  let B := 1+|log c|+|log D|
  have hD : 0<D := rpow_pos_of_pos p.bound_pos _
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro w hw
  have hR : 0 < 1+‖w‖ := by positivity
  have hv : 0 < ‖p.power t w‖ := norm_pos_iff.mpr (p.power_nonzero t hw)
  have hs := hscale w hw
  have hl := Real.log_le_log (div_pos hc (rpow_pos_of_pos hR t)) hs.1
  have hu := Real.log_le_log hv hs.2
  rw [Real.log_div hc.ne' (rpow_pos_of_pos hR t).ne',log_rpow hR] at hl
  change log ‖p.power t w‖ ≤ log (D/(1+‖w‖)^t) at hu
  rw [Real.log_div hD.ne' (rpow_pos_of_pos hR t).ne',log_rpow hR] at hu
  have hlog := log_nonneg (show 1 ≤ 1+‖w‖ by linarith [norm_nonneg w])
  dsimp [B]
  constructor
  · apply abs_le.mpr; constructor <;> linarith [le_abs_self (log c),neg_le_abs (log c),le_abs_self (log D),
      abs_nonneg (log D),abs_nonneg (log c),mul_nonneg ht.le hlog]
  · linarith [le_abs_self (log D),abs_nonneg (log c),neg_le_abs (log ‖p.power t w‖)]

theorem distance_to_reflection_bound (z w : ℂ) (hz : 0≤z.im) (hw : 0≤w.im) :
    ‖w-z‖ ≤ ‖w-conj z‖ := by
  have hh : ‖w-conj z‖^2 = ‖w-z‖^2+4*w.im*z.im := by
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.conj_im,Complex.conj_re]
    ring
  exact le_of_sq_le_sq (by nlinarith [mul_nonneg hw hz]) (norm_nonneg _)

def residualIntegrand (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (f w*((log ‖f z‖-log ‖f w‖:ℝ):ℂ))*conj (bergmanKernel z w)

theorem integrand_norm (f : ℂ → ℂ) (z w : ℂ) :
    ‖residualIntegrand f z w‖ = ‖f w‖*|log ‖f z‖-log ‖f w‖|/‖w-conj z‖^2 := by
  simp only [residualIntegrand,bergmanKernel,norm_mul,Complex.norm_conj,norm_neg,norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,div_eq_mul_inv]

/-- The logarithmic difference cancels one power of the local Bergman kernel singularity. -/
theorem PickSum.residual_near_bound {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0<t) :
    ∃ C > 0, ∀ z w : ℂ, z ∈ upper → w ∈ upper → ‖w-z‖ ≤ (1+‖z‖)/2 →
      ‖residualIntegrand (p.power t) z w‖ ≤ C/((1+‖z‖)^t*(1+‖z‖))*‖w-z‖⁻¹ := by
  obtain ⟨L,hL,hlog⟩ := p.log_power_oscillation ht
  obtain ⟨_,_,hscale⟩ := p.power_two_sided ht.le
  let U := p.bound^t
  have hU : 0<U := rpow_pos_of_pos p.bound_pos _
  refine ⟨U*(2:ℝ)^t*L,by positivity,?_⟩
  intro z w hz hw hnear
  rw [integrand_norm]
  by_cases he : w=z
  · simp [he]
  let R := 1+‖z‖
  let W := 1+‖w‖
  have hR : 0<R := by dsimp [R]; positivity
  have hW : 0<W := by dsimp [W]; positivity
  have hcomp : R ≤ 2*W := by
    have q := norm_add_le (z-w) w
    rw [sub_add_cancel,norm_sub_rev z w] at q
    dsimp [R,W]; linarith
  have hpow := rpow_le_rpow hR.le hcomp ht.le
  rw [mul_rpow (by norm_num) hW.le] at hpow
  have hb : ‖p.power t w‖ ≤ U*(2:ℝ)^t/R^t := by
    apply (hscale w (le_of_lt hw)).2.trans
    apply (div_le_div_iff₀ (rpow_pos_of_pos hW t) (rpow_pos_of_pos hR t)).mpr
    change U*R^t ≤ U*2^t*W^t
    nlinarith [mul_le_mul_of_nonneg_left hpow hU.le]
  have hx := hlog z w (le_of_lt hz) (le_of_lt hw) hnear
  rw [abs_sub_comm] at hx
  have dd := distance_to_reflection_bound z w (le_of_lt hz) (le_of_lt hw)
  have hδ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have dd' := hδ.trans_le dd
  have hnum := mul_le_mul hb hx (abs_nonneg _) (by positivity)
  apply (div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (abs_nonneg _)) (sq_pos_of_pos hδ)
    (pow_le_pow_left₀ hδ.le dd 2)).trans
  calc
    _ ≤ ((U*2^t/R^t)*(L*‖w-z‖/R))/‖w-z‖^2 := div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ = _ := by dsimp only [R]; field_simp [hδ.ne',hR.ne',(rpow_pos_of_pos hR t).ne'] <;> ring

end Liu
