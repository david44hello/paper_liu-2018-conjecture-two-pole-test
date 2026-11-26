import Liu.CitedInterpolation
import Liu.SlopeFormula

noncomputable section
open Set Filter Real Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace Liu

/-- Compensated second variation of the scalar trial norm. -/
def trialFactor (w : ℂ) (d : ℝ) : ℝ :=
  (‖1-(d:ℂ)*w‖^(2+d)-1+2*d*w.re)/d^2

theorem trial_sq (w : ℂ) (d : ℝ) :
    ‖1-(d:ℂ)*w‖^2 = 1-2*d*w.re+d^2*‖w‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.one_re,Complex.one_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

private theorem log_trial_deriv (w : ℂ) : HasDerivAt (fun t : ℝ => Real.log ‖1-(t:ℂ)*w‖) (-w.re) 0 := by
  let F := fun t : ℂ => Complex.log (1-t*w)
  have hd := ((((hasDerivAt_id (0:ℂ)).mul_const w).const_sub 1).clog (by simp : (1-id (0:ℂ)*w)∈Complex.slitPlane))
  have d : HasDerivAt F (-w) 0 := by simpa [F] using hd
  simpa only [F,Function.comp_def,Complex.log_re,Complex.neg_re,Complex.ofReal_zero] using
    (show HasDerivAt F (-w) ((0:ℝ):ℂ) by simpa using d).real_of_complex

theorem trialFactor_limit (w : ℂ) :
    Tendsto (trialFactor w) (𝓝[≠] 0) (𝓝 (‖w‖^2-w.re)) := by
  let N := fun d : ℝ => ‖1-(d:ℂ)*w‖
  have hn : ContinuousAt N 0 := by dsimp [N]; fun_prop
  have h0 : N 0=1 := by simp [N]
  have hpos : ∀ᶠ d in 𝓝 (0:ℝ), 0<N d := hn.eventually (Ioi_mem_nhds (by rw [h0]; norm_num))
  have hl : Tendsto (fun d : ℝ => Real.log (N d)/d) (𝓝[≠] 0) (𝓝 (-w.re)) := by
    have H : Tendsto (fun d : ℝ => slope (fun t : ℝ => Real.log ‖1-(t:ℂ)*w‖) 0 d) (𝓝[≠] 0) (𝓝 (-w.re)) := hasDerivAt_iff_tendsto_slope.mp (log_trial_deriv w)
    simpa [N,slope_def_field] using H
  let ex := dslope Real.exp 0
  have hex : ContinuousAt ex 0 := (continuousAt_dslope_same.mpr (Real.hasDerivAt_exp 0).differentiableAt)
  have exp0 : ex 0=1 := by simp [ex,Real.deriv_exp]
  have hsmall : Tendsto (fun d : ℝ => d*Real.log (N d)) (𝓝 0) (𝓝 0) := by
    simpa [h0] using (tendsto_id (x:=𝓝 (0:ℝ))).mul ((Real.continuousAt_log (by rw [h0]; norm_num)).comp hn).tendsto
  have h1 : Tendsto (fun d : ℝ => ex (d*Real.log (N d))) (𝓝[≠] 0) (𝓝 (ex 0)) := (hex.tendsto.comp hsmall).mono_left nhdsWithin_le_nhds
  rw [exp0] at h1
  have hN : Tendsto (fun d => N d^2) (𝓝[≠] 0) (𝓝 1) := by simpa [h0] using (hn.tendsto.pow 2).mono_left nhdsWithin_le_nhds
  have hL := (((hN.mul h1).mul hl).add_const (‖w‖^2))
  apply (show Tendsto (fun d : ℝ => N d^2*ex (d*Real.log (N d))*(Real.log (N d)/d)+‖w‖^2)
    (𝓝[≠] 0) (𝓝 (‖w‖^2-w.re)) by simpa [sub_eq_add_neg,add_comm,Function.comp_def] using hL).congr'
  filter_upwards [hpos.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with d hd hnz
  have hne : d≠0 := hnz
  have e := sub_smul_dslope Real.exp 0 (d*Real.log (N d))
  change _ * ex _ = _ at e
  simp only [sub_zero,Real.exp_zero] at e
  have sq := trial_sq w d
  change N d^2=_ at sq
  unfold trialFactor
  change _=(N d^(2+d)-1+2*d*w.re)/d^2
  rw [Real.rpow_add hd,Real.rpow_two,Real.rpow_def_of_pos hd,mul_comm (Real.log (N d)) d]
  rw [show Real.exp (d*Real.log (N d))=1+(d*Real.log (N d))*ex (d*Real.log (N d)) by linarith [e]]
  field_simp [hne]
  linear_combination -sq

end Liu
