import Liu.RayAngles

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

/-- A smooth branch for the polar angle across both real edges of the upper
half-plane, away from the origin. -/
def upperAngle (z : ℂ) := π/2+(Complex.log (-Complex.I*z)).im

theorem upperAngle_eq {z : ℂ} (hz : 0≤z.im) (hn : z≠0) : upperAngle z=z.arg := by
  have h₀ := Complex.arg_nonneg_iff.mpr hz
  have hπ := Complex.arg_le_pi z
  have hsum : (-Complex.I).arg+z.arg ∈ Ioc (-π) π := by
    rw [Complex.arg_neg_I]; constructor <;> linarith [pi_pos]
  rw [upperAngle,Complex.log_im,Complex.arg_mul (neg_ne_zero.mpr Complex.I_ne_zero) hn hsum,Complex.arg_neg_I]
  ring

private theorem angle_slit {z : ℂ} (hz : 0≤z.im) (hn : z≠0) : -Complex.I*z∈Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    neg_zero,zero_mul,neg_one_mul,sub_neg_eq_add,zero_add]
  rcases hz.eq_or_lt with he | hp
  · right
    intro h
    apply hn
    apply Complex.ext <;> simp_all <;> linarith
  · exact Or.inl hp

def angleDifferential (z : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM.comp (z⁻¹ • (1:ℂ →L[ℝ] ℂ))

theorem upperLog_hasDerivAt {z : ℂ} (hz : 0≤z.im) (hn : z≠0) :
    HasDerivAt (fun w : ℂ => Complex.log (-Complex.I*w)) z⁻¹ z := by
  have hd := ((hasDerivAt_id z).const_mul (-Complex.I)).clog (angle_slit hz hn)
  convert hd using 1
  · rfl
  · simp only [id_eq,mul_one]
    field_simp [hn,Complex.I_ne_zero] <;> ring

theorem upperAngle_hasFDerivAt {z : ℂ} (hz : 0≤z.im) (hn : z≠0) :
    HasFDerivAt upperAngle (angleDifferential z) z :=
  (Complex.imCLM.hasFDerivAt.comp z (upperLog_hasDerivAt hz hn).complexToReal_fderiv).const_add (π/2)

def angularPotential (m : ℝ) (z : ℂ) : ℂ :=
  Complex.I*((m/2*upperAngle z*(π-upperAngle z):ℝ):ℂ)

def angularDifferential (m : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (angleDifferential z).smulRight (Complex.I*((m*(π/2-upperAngle z):ℝ):ℂ))

theorem angularDifferential_apply (m : ℝ) (z h : ℂ) :
    angularDifferential m z h = Complex.I*((m*(π/2-upperAngle z)*(h/z).im:ℝ):ℂ) := by
  unfold angularDifferential angleDifferential
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply,Complex.imCLM_apply,Complex.real_smul,smul_eq_mul,Complex.ofReal_mul,
    div_eq_mul_inv,mul_comm z⁻¹ h]
  ring

theorem angularPotential_hasFDerivAt (m : ℝ) {z : ℂ} (hz : 0≤z.im) (hn : z≠0) :
    HasFDerivAt (angularPotential m) (angularDifferential m z) z := by
  have h := upperAngle_hasFDerivAt hz hn
  have dr := (h.const_mul (m/2)).mul (h.const_sub π)
  have dc := (Complex.ofRealCLM.hasFDerivAt.comp z dr).const_mul Complex.I
  convert dc using 1
  · rfl
  · ext w
    simp [angularDifferential,ContinuousLinearMap.smulRight_apply,Complex.real_smul]
    push_cast; ring

theorem angularPotential_eq (m : ℝ) {z : ℂ} (hz : 0≤z.im) (hn : z≠0) :
    angularPotential m z=Complex.I*((m/2*z.arg*(π-z.arg):ℝ):ℂ) := by rw [angularPotential,upperAngle_eq hz hn]

end Liu
