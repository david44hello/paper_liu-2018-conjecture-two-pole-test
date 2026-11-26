import Liu.LogRay
import Liu.PolarRays

noncomputable section
open Set Real
open scoped ComplexConjugate
namespace Liu

private theorem phase_sub (a b : ℝ) : unitPhase (a-b)=unitPhase a/unitPhase b := by
  unfold unitPhase; rw [Complex.ofReal_sub,sub_mul,Complex.exp_sub]

private theorem phase_add (a b : ℝ) : unitPhase (a+b)=unitPhase a*unitPhase b := by
  unfold unitPhase; rw [Complex.ofReal_add,add_mul,Complex.exp_add]

private theorem phase_conj (a : ℝ) : conj (unitPhase a)=(unitPhase a)⁻¹ := by
  unfold unitPhase
  rw [←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,Complex.exp_neg]

private theorem phase_pi : unitPhase π = -1 := Complex.exp_pi_mul_I
private theorem phase_neg_pi : unitPhase (-π) = -1 := by
  simp [unitPhase,Complex.ofReal_neg,neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I]

private theorem ray_log_polar {r θ : ℝ} (hr : 0<r) (hθ : θ∈Ioo (-π) π) :
    polarRay r θ ∈ Complex.slitPlane ∧ Complex.log (polarRay r θ) = (log r:ℂ)+(θ:ℂ)*Complex.I := by
  have he : Complex.log (unitPhase θ)=(θ:ℂ)*Complex.I :=
    Complex.log_exp (by simpa using hθ.1) (by simpa using hθ.2.le)
  have hn := Complex.exp_ne_zero ((θ:ℂ)*Complex.I)
  have hlog : Complex.log (polarRay r θ)=_ := (Complex.log_ofReal_mul hr hn).trans (congrArg (fun v => (log r:ℂ)+v) he)
  refine ⟨Complex.mem_slitPlane_iff_arg.mpr ⟨?_,mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hn⟩,hlog⟩
  have hi := congrArg Complex.im hlog
  simp only [Complex.log_im,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] at hi
  rw [hi]; exact hθ.2.ne

theorem upper_arg_range {z : ℂ} (hz : z∈upper) : z.arg∈Ioo (0:ℝ) π := by
  have hi : 0<z.im := hz
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hi.le) ?_,Complex.arg_lt_pi_iff.mpr (Or.inr hi.ne')⟩
  intro e
  have h := Complex.sin_arg z
  rw [←e,Real.sin_zero] at h
  have hp := div_pos hi (hi.trans_le (Complex.im_le_norm _))
  linarith

/-- The jump between the two principal ray logarithms across the observation
angle. Both logarithms have the same radial real part. -/
theorem reflected_ray_logs {z : ℂ} (hz : 0≤z.im) (hnz : z≠0) {φ : ℝ} (hφ : φ∈Ioo (0:ℝ) π) (hne : φ≠z.arg) :
    -(conj (unitPhase φ))/z ∈ Complex.slitPlane ∧ -(unitPhase φ)/z ∈ Complex.slitPlane ∧
    Complex.log (-(unitPhase φ)/z)-Complex.log (-(conj (unitPhase φ))/z) =
      (2*Complex.I)*((if φ<z.arg then φ else φ-π:ℝ):ℂ) := by
  let θ := z.arg
  let r := ‖z‖
  have ht : θ∈Icc (0:ℝ) π := ⟨Complex.arg_nonneg_iff.mpr hz,Complex.arg_le_pi _⟩
  have hr : 0<r := norm_pos_iff.mpr hnz
  have zrep : z=(r:ℂ)*unitPhase θ := (Complex.norm_mul_exp_arg_mul_I z).symm
  have ref : -(conj (unitPhase φ))/z = polarRay r⁻¹ (π-φ-θ) := by
    rw [zrep,polarRay,phase_sub,phase_sub,phase_pi,phase_conj,Complex.ofReal_inv]
    simp only [div_eq_mul_inv,mul_inv_rev]; ring
  obtain ⟨ha,hA⟩ := ray_log_polar (inv_pos.mpr hr) (show π-φ-θ ∈ Ioo (-π) π from
    ⟨by linarith [ht.2,hφ.2],by linarith [ht.1,hφ.1]⟩)
  rw [ref]
  refine ⟨ha,?_⟩
  by_cases ho : φ<θ
  · have eqn : -(unitPhase φ)/z=polarRay r⁻¹ (π+φ-θ) := by
      rw [zrep,polarRay,phase_sub,phase_add,phase_pi,Complex.ofReal_inv]
      simp only [div_eq_mul_inv,mul_inv_rev]; ring
    obtain ⟨hb,hB⟩ := ray_log_polar (inv_pos.mpr hr) (show π+φ-θ ∈ Ioo (-π) π from
      ⟨by linarith [pi_pos,ht.2,hφ.1],by linarith⟩)
    rw [eqn,if_pos ho,hA,hB]
    exact ⟨hb,by push_cast; ring⟩
  · have hlt : θ<φ := lt_of_le_of_ne (le_of_not_gt ho) hne.symm
    have eqn : -(unitPhase φ)/z=polarRay r⁻¹ (-π+φ-θ) := by
      rw [zrep,polarRay,phase_sub,phase_add,phase_neg_pi,Complex.ofReal_inv]
      simp only [div_eq_mul_inv,mul_inv_rev]; ring
    obtain ⟨hb,hB⟩ := ray_log_polar (inv_pos.mpr hr) (show -π+φ-θ ∈ Ioo (-π) π from
      ⟨by linarith,by linarith [pi_pos,ht.1,hφ.2]⟩)
    rw [eqn,if_neg ho,hA,hB]
    exact ⟨hb,by push_cast; ring⟩

end Liu
