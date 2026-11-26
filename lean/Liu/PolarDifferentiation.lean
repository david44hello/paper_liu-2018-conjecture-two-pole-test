import Liu.AngularPotential
import Liu.LogSource

noncomputable section
open Real
open scoped ComplexConjugate
namespace Liu

/-- A potential written as a product in log-radius and angle. -/
def polarProduct (a y : ℝ → ℂ) (z : ℂ) := a (log ‖z‖)*y (upperAngle z)

def polarDifferential (z A B : ℂ) : ℂ →L[ℝ] ℂ :=
  (Complex.reCLM.comp (z⁻¹ • (1:ℂ →L[ℝ] ℂ))).smulRight A + (angleDifferential z).smulRight B

theorem polarDifferential_apply (z A B h : ℂ) :
    polarDifferential z A B h = (((z⁻¹*h).re:ℝ):ℂ)*A + (((z⁻¹*h).im:ℝ):ℂ)*B := by
  simp [polarDifferential,angleDifferential,Complex.real_smul]

theorem polarProduct_hasFDerivAt {a y : ℝ → ℂ} {z a' y' : ℂ} (hz : 0≤z.im) (hn : z≠0)
    (da : HasDerivAt a a' (log ‖z‖)) (dy : HasDerivAt y y' (upperAngle z)) :
    HasFDerivAt (polarProduct a y) (polarDifferential z (a'*y (upperAngle z)) (a (log ‖z‖)*y')) z := by
  have dl := Complex.reCLM.hasFDerivAt.comp z (upperLog_hasDerivAt hz hn).complexToReal_fderiv
  have de : (fun w : ℂ => (Complex.log (-Complex.I*w)).re) = fun w : ℂ => log ‖w‖ := by
    funext w; simp [Complex.log_re]
  change HasFDerivAt (fun w : ℂ => (Complex.log (-Complex.I*w)).re) _ z at dl
  rw [de] at dl
  have d := (da.hasFDerivAt.comp z dl).mul (dy.hasFDerivAt.comp z (upperAngle_hasFDerivAt hz hn))
  convert d using 1
  · rfl
  ext h
  simp [polarDifferential,angleDifferential,Complex.real_smul]; ring

/-- Both Wirtinger combinations of a differential in log-polar coordinates. -/
theorem polarDifferential_wirtinger (z A B : ℂ) :
    polarDifferential z A B 1-Complex.I*polarDifferential z A B Complex.I=z⁻¹*(A-Complex.I*B) ∧
    polarDifferential z A B 1+Complex.I*polarDifferential z A B Complex.I=conj (z⁻¹)*(A+Complex.I*B) := by
  have hr := Complex.re_add_im (z⁻¹)
  have hc := congrArg (starRingEnd ℂ) hr
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I] at hc
  simp only [polarDifferential_apply,mul_one,Complex.mul_I_re,Complex.mul_I_im,Complex.ofReal_neg]
  constructor
  · conv_rhs => rw [←hr]
    ring_nf <;> simp [Complex.I_sq] <;> ring
  · conv_rhs => rw [←hc]
    ring_nf <;> simp [Complex.I_sq] <;> ring

def polarField (a a' y y' : ℝ → ℂ) (z : ℂ) : ℂ :=
  z⁻¹*(-polarProduct a' y z+Complex.I*polarProduct a y' z)

theorem polarProduct_field {a a' y y' : ℝ → ℂ} {z : ℂ} (hz : 0≤z.im) (hn : z≠0)
    (da : HasDerivAt a (a' (log ‖z‖)) (log ‖z‖)) (dy : HasDerivAt y (y' (upperAngle z)) (upperAngle z)) :
    - (fderiv ℝ (polarProduct a y) z 1-Complex.I*fderiv ℝ (polarProduct a y) z Complex.I) = polarField a a' y y' z := by
  rw [(polarProduct_hasFDerivAt hz hn da dy).fderiv,(polarDifferential_wirtinger ..).1]
  dsimp [polarField,polarProduct]; ring

theorem polarField_dbar {a a' a'' y y' y'' : ℝ → ℂ} {z : ℂ} (hz : 0≤z.im) (hn : z≠0)
    (da : HasDerivAt a (a' (log ‖z‖)) (log ‖z‖)) (dda : HasDerivAt a' (a'' (log ‖z‖)) (log ‖z‖))
    (dy : HasDerivAt y (y' (upperAngle z)) (upperAngle z)) (ddy : HasDerivAt y' (y'' (upperAngle z)) (upperAngle z)) :
    DifferentiableAt ℝ (polarField a a' y y') z ∧
      dbar (polarField a a' y y') z =
      -(polarProduct a'' y z+polarProduct a y'' z)/(2*(‖z‖:ℂ)^2) := by
  let H := fun w => -polarProduct a' y w+Complex.I*polarProduct a y' w
  have d1 := polarProduct_hasFDerivAt hz hn dda dy
  have d2 := polarProduct_hasFDerivAt hz hn da ddy
  have dH := d1.neg.add (d2.const_mul Complex.I)
  have hol := (hasDerivAt_id z).inv hn
  have dr := hol.complexToReal_fderiv.mul dH
  change HasFDerivAt (polarField a a' y y') _ z at dr
  refine ⟨dr.differentiableAt,?_⟩
  let A := a'' (log ‖z‖)*y (upperAngle z)
  let B := a' (log ‖z‖)*y' (upperAngle z)
  let C := a (log ‖z‖)*y'' (upperAngle z)
  have hb : z⁻¹*conj (z⁻¹) = ((‖z‖:ℂ)^2)⁻¹ := by rw [map_inv₀,←mul_inv,Complex.mul_conj']
  rw [dbar,dr.fderiv]
  simp only [add_apply,smul_apply,neg_apply,one_apply_eq_self,smul_eq_mul,mul_one,Pi.add_apply,
    Pi.neg_apply,Pi.mul_apply,Function.comp_apply,id_eq]
  have h1 := (polarDifferential_wirtinger z A B).2
  have h2 := (polarDifferential_wirtinger z B C).2
  change _ = -(A+C)/(2*(‖z‖:ℂ)^2)
  linear_combination (norm := (ring_nf; simp [Complex.I_sq]; ring)) -z⁻¹/2*h1 +
    (Complex.I*z⁻¹/2)*h2 -(A+C)/2*hb

end Liu
