import Liu.LinePole
import Mathlib.Probability.Distributions.Cauchy

noncomputable section
open MeasureTheory Filter Set Real ProbabilityTheory
open scoped Topology ComplexConjugate
namespace Liu

theorem linePole_sq (a b x : ℝ) :
    ‖linePole a b x‖^2 = ((x-a)^2+b^2)⁻¹ := by
  simp only [linePole,norm_inv,inv_pow,Complex.sq_norm,Complex.normSq_apply]
  simp [pow_two,Complex.mul_re,Complex.mul_im]

theorem linePole_sq_integrable (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x => ‖linePole a b x‖^2) volume := by
  let γ : NNReal := ⟨b,hb.le⟩
  have h := (integrable_cauchyPDFReal (x₀:=a) (γ:=γ)).const_mul (π/b)
  apply h.congr
  filter_upwards with x
  rw [linePole_sq,cauchyPDFReal_def]
  change π/b*(π⁻¹*b*((x-a)^2+b^2)⁻¹) = _
  field_simp [hb.ne',pi_ne_zero]

theorem linePair_integrable (a c : ℝ) {b d : ℝ} (hb : 0<b) (hd : 0<d) :
    Integrable (fun x => linePole a b x*conj (linePole c d x)) volume := by
  have h := (linePole_sq_integrable a hb).add (linePole_sq_integrable c hd)
  apply h.mono'
  · exact ((linePole_continuous a hb).mul (Complex.continuous_conj.comp (linePole_continuous c hd))).aestronglyMeasurable
  filter_upwards with x
  simp only [norm_mul,Complex.norm_conj,Pi.add_apply]
  nlinarith [sq_nonneg (‖linePole a b x‖-‖linePole c d x‖),sq_nonneg ‖linePole a b x‖,sq_nonneg ‖linePole c d x‖]

/-- Real-axis pairing of two lower-half-plane resolvents by symmetric integration.
All endpoints and the coincident-pole case are covered when both depths are positive. -/
theorem linePair_integral (a c : ℝ) {b d : ℝ} (hb : 0<b) (hd : 0<d) :
    ∫ x, linePole a b x*conj (linePole c d x) =
      2*(π:ℂ)*Complex.I/((c-a:ℝ)+(b+d:ℝ)*Complex.I) := by
  let D : ℂ := (c-a:ℝ)+(b+d:ℝ)*Complex.I
  have hn : D ≠ 0 := fun he => by
    have hi := congrArg Complex.im he
    simp [D] at hi; linarith
  have hpartial (x : ℝ) : linePole a b x*conj (linePole c d x) =
      (conj (linePole c d x)-linePole a b x)/D := by
    have ha : ((x-a:ℝ):ℂ)+(b:ℂ)*Complex.I ≠ 0 := fun he => by
      have hi := congrArg Complex.im he; simp at hi; linarith
    have hc : ((x-c:ℝ):ℂ)+(d:ℂ)*(-Complex.I) ≠ 0 := fun he => by
      have hi := congrArg Complex.im he; simp at hi; linarith
    simp only [linePole,map_inv₀,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
    let X : ℂ := ((x-a:ℝ):ℂ)+(b:ℂ)*Complex.I
    let Y : ℂ := ((x-c:ℝ):ℂ)+(d:ℂ)*(-Complex.I)
    change X⁻¹*Y⁻¹=(Y⁻¹-X⁻¹)/D
    have hXY : D = X-Y := by dsimp [D,X,Y]; push_cast; ring
    have hX : X ≠ 0 := ha
    have hY : Y ≠ 0 := hc
    apply (eq_div_iff hn).mpr
    rw [hXY]
    field_simp [hX,hY] <;> ring
  have hconj (R : ℝ) : ∫ x in -R..R, conj (linePole c d x) =
      conj (∫ x in -R..R, linePole c d x) := by
    simpa only [ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply] using
      Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
        ((linePole_continuous c hd).intervalIntegrable (μ:=volume) (-R) R)
  have hupper := Complex.continuous_conj.continuousAt.tendsto.comp (linePole_principal_value c hd)
  have hlow := linePole_principal_value a hb
  have hlim := (hupper.sub hlow).div_const D
  have hi := intervalIntegral_tendsto_integral (linePair_integrable a c hb hd) tendsto_neg_atTop_atBot
    (tendsto_id (α:=ℝ))
  apply tendsto_nhds_unique hi
  convert hlim using 1
  · funext R
    simp_rw [hpartial,div_eq_mul_inv,intervalIntegral.integral_mul_const]
    have hj : IntervalIntegrable (fun x => conj (linePole c d x)) volume (-R) R :=
      (Complex.continuous_conj.comp (linePole_continuous c hd)).intervalIntegrable ..
    simp only [id_eq,Function.comp_apply]
    rw [intervalIntegral.integral_sub hj
      ((linePole_continuous a hb).intervalIntegrable ..),hconj]
  · congr 1
    simp [D,Complex.conj_I]
    ring

end Liu
