import Liu.RationalLogTerm

noncomputable section
open Set Real MeasureTheory
open scoped ComplexConjugate
namespace Liu

private theorem conjugate_log_parts (L : ℂ) : conj L = L-2*(L.im:ℂ)*Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring

/-- On the diagonal of the two pole parameters the general log term is the
known single-pole field, even when the observing point equals the partner. -/
theorem diagonal_log_field {p z : ℂ} (hp : p.im<0) (hz : 0≤z.im) :
    field (pole 1 p) z = (Complex.I/2)*rationalLogTerm p (conj p) z := by
  let x := p.re
  let b := -p.im
  let u := (z-(x:ℂ))/(b:ℂ)
  let Y := z-p
  let D := conj p-p
  let L := Complex.log Y - Complex.log D
  let B := logChord p (conj p) z
  have hb : 0<b := neg_pos.mpr hp
  have hbC := Complex.ofReal_ne_zero.mpr hb.ne'
  have hq : 0<(conj p).im := by simpa using hp
  have hp' : ((x:ℂ)-(b:ℂ)*Complex.I)=p := by dsimp [x,b]; apply Complex.ext <;> simp
  have hq' : ((x:ℂ)+(b:ℂ)*Complex.I)=conj p := by dsimp [x,b]; apply Complex.ext <;> simp
  have hD : D=2*(b:ℂ)*Complex.I := by dsimp [D]; rw [←hq',←hp']; ring
  have hY : 0<Y.im := by dsimp [Y]; simp; linarith
  have hnY : Y≠0 := by intro e; simp [e] at hY
  have hu : 0≤u.im := by dsimp [u]; simp [div_eq_mul_inv,Complex.mul_im]; positivity
  have hω : omegaCorrection u = (b:ℂ)*B := by
    rw [omegaCorrection_integral hu]
    dsimp only [B,logChord]
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    have hd : conj p+(t:ℂ)*(z-conj p)-p = (b:ℂ)*(2*Complex.I+(t:ℂ)*(u-Complex.I)) := by
      dsimp [u]; rw [←hq',←hp']; field_simp [hbC] <;> ring
    dsimp only
    rw [hd,mul_inv_rev]
    field_simp [hbC]
  have hmul : (z-conj p)*B=L := by
    dsimp only [B,L,Y,D]
    rw [logChord_eq hp hq hz]
    exact sub_smul_dslope (fun w => Complex.log (w-p)) (conj p) z
  have hT : rationalLogTerm p (conj p) z = conj L/Y-B := by
    rw [rationalLogTerm_physical hp hp hz,←logChord_eq hp hq hz]
    simp [L,Y,D,B]
  have harg : (-1/Y).arg=π-Y.arg := by
    have hh := congrArg Real.Angle.toReal (Complex.arg_div_coe_angle (by norm_num : (-1:ℂ)≠0) hnY)
    obtain ⟨hl,hr⟩ := upper_arg_range (z:=Y) hY
    simpa only [Complex.arg_neg_one,←Real.Angle.coe_sub,Complex.arg_coe_angle_toReal_eq_arg,
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr (show π-Y.arg ∈ Ioc (-π) π from ⟨by linarith [pi_pos],by linarith⟩)] using hh
  have hIm : L.im=Y.arg-π/2 := by
    dsimp only [L]
    rw [Complex.sub_im,Complex.log_im,Complex.log_im,hD]
    have hB' : (2:ℂ)*(b:ℂ)=((2*b:ℝ):ℂ) := by push_cast; rfl
    rw [hB',Complex.arg_real_mul _ (by positivity),Complex.arg_I]
  have hSp : pole 1 p z = -1/Y := by simp [pole,Y]
  have hS := singlePole_optimalWitness x (a:=1) zero_lt_one hb hz
  rw [hp'] at hS
  change (pole 1 p z*((pole 1 p z).arg:ℂ)-field (pole 1 p) z)/(pole 1 p z) = ((π/2:ℝ):ℂ)+omegaCorrection u at hS
  rw [hSp,harg,hω] at hS
  have he : field (pole 1 p) z * Y = (L.im:ℂ)+(b:ℂ)*B := by
    rw [hIm]; push_cast at hS ⊢
    field_simp [hnY] at hS
    linear_combination hS / 2
  rw [hT,conjugate_log_parts]
  apply (mul_left_inj' hnY).mp
  rw [he]
  have hd : z-conj p = Y-2*(b:ℂ)*Complex.I := by dsimp [Y]; rw [←hq',←hp']; ring
  rw [hd] at hmul
  rw [←hmul]
  field_simp [hnY]
  ring_nf <;> simp [Complex.I_sq] <;> ring

end Liu
