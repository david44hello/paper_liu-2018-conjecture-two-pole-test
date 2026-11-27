module

public import Liu.AngularDeficit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

def amplitude (t : ℝ) : ℂ := ((1+t:ℝ):ℂ)/(2*Complex.I*(t:ℂ))
def correction (t : ℝ) : ℂ := (π:ℂ)*Complex.exp ((t*π:ℝ)*Complex.I)/(sin (t*π):ℝ)
def phase (t : ℝ) (x : ℂ) : ℂ := Complex.exp ((t:ℂ)*x*Complex.I)

def angularSolution (t : ℝ) (x : ℂ) : ℂ :=
  if t=0 then x*(x-(π:ℂ))/2 else amplitude t*(x*phase t x-correction t*Complex.sin ((t:ℂ)*x))

private def angularD (t : ℝ) (x : ℂ) : ℂ :=
  amplitude t*(phase t x + x*(phase t x*((t:ℂ)*Complex.I))-
    correction t*(Complex.cos ((t:ℂ)*x)*(t:ℂ)))

private theorem phase_deriv (t : ℝ) (x : ℂ) :
    HasDerivAt (phase t) (phase t x*((t:ℂ)*Complex.I)) x := by
  unfold phase
  simpa only [id_eq,mul_one] using ((((hasDerivAt_id x).const_mul (t:ℂ)).mul_const Complex.I).cexp)

private theorem angularSolution_deriv (t : ℝ) (ht : t≠0) (x : ℂ) : HasDerivAt (angularSolution t) (angularD t x) x := by
  have h := ((hasDerivAt_id x).const_mul (t:ℂ)).csin
  unfold angularSolution angularD
  simp only [if_neg ht]
  simpa [id_eq] using
    (((hasDerivAt_id x).mul (phase_deriv t x)).sub (h.const_mul (correction t))).const_mul (amplitude t)

theorem angularSolution_dirichlet {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    angularSolution t 0=0 ∧ angularSolution t (π:ℂ)=0 ∧
    ∀ x : ℂ, deriv (deriv (angularSolution t)) x + (t:ℂ)^2*angularSolution t x =
      ((1+t:ℝ):ℂ)*Complex.exp ((t:ℂ)*x*Complex.I) := by
  change _ ∧ _ ∧ ∀ x : ℂ, _ = ((1+t:ℝ):ℂ)*phase t x
  have hs := sin_pos_of_pos_of_lt_pi (mul_pos ht pi_pos) (by nlinarith [mul_lt_mul_of_pos_right ht1 pi_pos])
  constructor
  · simp [angularSolution,ht.ne']
  constructor
  · simp [angularSolution,ht.ne',phase,correction,Complex.ofReal_mul,Complex.ofReal_sin,
      Complex.ofReal_ne_zero.mpr hs.ne',show Complex.sin ((t:ℂ)*(π:ℂ))≠0 by
        simpa only [←Complex.ofReal_mul,←Complex.ofReal_sin,ne_eq,Complex.ofReal_eq_zero] using hs.ne']
  intro x
  have dp := phase_deriv t x
  have dcos := ((hasDerivAt_id x).const_mul (t:ℂ)).ccos
  have d := ((dp.add ((hasDerivAt_id x).mul (dp.mul_const ((t:ℂ)*Complex.I)))).sub
    ((dcos.mul_const (t:ℂ)).const_mul (correction t))).const_mul (amplitude t)
  rw [show deriv (angularSolution t)=angularD t by funext y; exact (angularSolution_deriv t ht.ne' y).deriv]
  rw [show deriv (angularD t) x = _ from d.deriv]
  simp only [id_eq,angularSolution,if_neg ht.ne',amplitude]
  field_simp [Complex.I_ne_zero,Complex.ofReal_ne_zero.mpr ht.ne']
  ring_nf <;> simp [Complex.I_sq] <;> ring

/-- The restriction to real angles solves the classical boundary value problem. -/
theorem angularSolution_real_system {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    ∃ v : ℝ → ℂ, ∀ x : ℝ, HasDerivAt (fun u : ℝ => angularSolution t u) (v x) x ∧
      HasDerivAt v (((1+t:ℝ):ℂ)*Complex.exp ((t:ℂ)*x*Complex.I) - (t:ℂ)^2*angularSolution t x) x := by
  refine ⟨fun x => angularD t x,?_⟩
  intro x
  refine ⟨(angularSolution_deriv t ht.ne' (x:ℂ)).comp_ofReal,?_⟩
  have hd : DifferentiableAt ℂ (angularD t) (x:ℂ) := by unfold angularD phase; fun_prop
  have he := (angularSolution_dirichlet ht ht1).2.2 (x:ℂ)
  rw [show deriv (angularSolution t) = angularD t by funext u; exact (angularSolution_deriv t ht.ne' u).deriv] at he
  rw [←eq_sub_of_add_eq he]
  exact hd.hasDerivAt.comp_ofReal

def angularEnergy (t : ℝ) := (1/π)*∫ x in Ioo (0:ℝ) π,
  ‖(t:ℂ)*angularSolution t x+Complex.I*deriv (fun u : ℝ => angularSolution t u) x‖^2

private theorem angular_flux {t : ℝ} (ht : 0<t) (x : ℝ) :
    (t:ℂ)*angularSolution t x+Complex.I*deriv (fun u : ℝ => angularSolution t u) x =
    (((1+t)/(2*t):ℝ):ℂ)*(phase t x-
      ((t*π/sin (t*π):ℝ):ℂ)*phase t ((π-x:ℝ):ℂ)) := by
  rw [(angularSolution_deriv t ht.ne' (x:ℂ)).comp_ofReal.deriv]
  have he : phase t ((π-x:ℝ):ℂ) = phase t (π:ℂ)*Complex.exp (-((t:ℂ)*(x:ℂ))*Complex.I) := by
    unfold phase; rw [←Complex.exp_add,Complex.ofReal_sub]; congr 1; ring
  rw [he,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg]
  simp only [angularSolution,if_neg ht.ne',angularD,amplitude,correction,phase,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_ofNat]
  field_simp [Complex.I_ne_zero,Complex.ofReal_ne_zero.mpr ht.ne'] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private theorem phases_norm (t x y a : ℝ) :
    ‖phase t x-(a:ℂ)*phase t y‖^2 = 1+a^2-2*a*cos (t*x-t*y) := by
  simp only [phase,Complex.sq_norm,Complex.normSq_apply,Complex.exp_mul_I,←Complex.ofReal_mul,
    ←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  rw [cos_sub]
  nlinarith only [sin_sq_add_cos_sq (t*x),congrArg (fun v : ℝ => a^2*v) (sin_sq_add_cos_sq (t*y))]

/-- Closed expression for the angular mean in Appendix B, Step 3. -/
theorem angularEnergy_eq {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    angularEnergy t = ((1+t)/(2*t))^2*((t*π/sin (t*π))^2-1) := by
  let a := t*π/sin (t*π)
  have hs := sin_pos_of_pos_of_lt_pi (mul_pos ht pi_pos) (by nlinarith [mul_lt_mul_of_pos_right ht1 pi_pos])
  have hcos : (∫ x in Ioo (0:ℝ) π, cos (t*x-t*(π-x)))=sin (t*π)/t := by
    rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le pi_pos.le]
    let F := fun x : ℝ => sin (2*t*x-t*π)/(2*t)
    have hd (x : ℝ) : HasDerivAt F (cos (t*x-t*(π-x))) x := by
      have d := ((((hasDerivAt_id x).const_mul (2*t)).sub_const (t*π)).sin).div_const (2*t)
      convert d using 1
      · rfl
      · rw [show t*x-t*(π-x)=2*t*x-t*π by ring]
        simp [id_eq,ht.ne']
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (by apply Continuous.intervalIntegrable; fun_prop)]
    simp [F,show 2*t*π-t*π=t*π by ring]; field_simp [ht.ne']; ring
  have hC : IntegrableOn (fun x : ℝ => cos (t*x-t*(π-x))) (Ioo 0 π) := by
    apply (Continuous.integrableOn_Icc (by fun_prop : Continuous (fun x : ℝ => cos (t*x-t*(π-x))))).mono_set Ioo_subset_Icc_self
  have hconst : IntegrableOn (fun _ : ℝ => 1+a^2) (Ioo 0 π) := integrableOn_const (measure_Ioo_lt_top.ne)
  unfold angularEnergy
  simp_rw [angular_flux ht,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,phases_norm]
  rw [integral_const_mul,integral_sub hconst (hC.const_mul (2*a)),integral_const_mul,hcos,setIntegral_const,
    Real.volume_real_Ioo_of_le pi_pos.le,smul_eq_mul,sub_zero]
  dsimp only [a]
  have hs' : sin (π*t)≠0 := by simpa only [mul_comm π t] using hs.ne'
  field_simp [pi_ne_zero,ht.ne',hs.ne',hs'] <;> ring_nf <;> simp [hs']

end Liu
