import Liu.CutoffProfile
import Liu.PolarDifferentiation
import Liu.ExteriorSource

noncomputable section
open Set Real Filter
open scoped ComplexConjugate Topology
namespace Liu

def modelAngular (t x : ℝ) := angularSolution t (x:ℂ)
def modelAngularD (t : ℝ) := deriv (modelAngular t)
def modelAngularDD (t x : ℝ) : ℂ :=
  ((1+t:ℝ):ℂ)*Complex.exp ((t:ℂ)*(x:ℂ)*Complex.I)-(t:ℂ)^2*modelAngular t x

theorem modelAngular_derivatives {t : ℝ} (ht : 0<t) (ht1 : t<1) (x : ℝ) :
    HasDerivAt (modelAngular t) (modelAngularD t x) x ∧
    HasDerivAt (modelAngularD t) (modelAngularDD t x) x ∧ DifferentiableAt ℝ (modelAngularDD t) x := by
  obtain ⟨v,hv⟩ := angularSolution_real_system ht ht1
  have he : modelAngularD t=v := by funext u; exact (hv u).1.deriv
  rw [he]
  refine ⟨(hv x).1,(hv x).2,?_⟩
  have hy : DifferentiableAt ℝ (modelAngular t) x := (hv x).1.differentiableAt
  unfold modelAngularDD
  fun_prop

/-- The coefficient converts the unit angular solution to the physical source
of total mass m, using the upper determination of the argument. -/
def modelCoefficient (m t : ℝ) : ℂ := -((m^(1+t):ℝ):ℂ)*Complex.exp (-(t:ℂ)*(π:ℂ)*Complex.I)

theorem norm_modelCoefficient {m : ℝ} (hm : 0 < m) (t : ℝ) :
    ‖modelCoefficient m t‖=m^(1+t) := by
  simp [modelCoefficient,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.mul_im,abs_of_pos (rpow_pos_of_pos hm _)]

def cutoffPotential (m t : ℝ) (z : ℂ) : ℂ := if z=0 then 0 else
  modelCoefficient m t*polarProduct (modelRadial t) (modelAngular t) z

def cutoffField (m t : ℝ) (z : ℂ) : ℂ := if z=0 then 0 else
  modelCoefficient m t*polarField (modelRadial t) (modelRadialD t) (modelAngular t) (modelAngularD t) z

def cutoffSource (m t : ℝ) (z : ℂ) : ℂ := if z=0 then 0 else
  modelCoefficient m t*(-(polarProduct (modelRadialDD t) (modelAngular t) z+
    polarProduct (modelRadial t) (modelAngularDD t) z)/(2*(‖z‖:ℂ)^2))

theorem cutoff_zero_on_ball (m t : ℝ) {z : ℂ} (hr : ‖z‖<1) :
    cutoffPotential m t z=0 ∧ cutoffField m t z=0 ∧ cutoffSource m t z=0 := by
  by_cases hn : z=0
  · simp [cutoffPotential,cutoffField,cutoffSource,hn]
  obtain ⟨h₀,h₁,h₂⟩ := modelRadial_near_zero t (log_neg (norm_pos_iff.mpr hn) hr)
  simp [cutoffPotential,cutoffField,cutoffSource,hn,polarField,polarProduct,h₀,h₁,h₂]

theorem cutoffPotential_gradient (m : ℝ) {t : ℝ} (ht : 0<t) (ht1 : t<1) {z : ℂ} (hz : 0≤z.im) (hn : z≠0) :
    DifferentiableAt ℝ (cutoffPotential m t) z ∧ cutoffField m t z =
      -(fderiv ℝ (cutoffPotential m t) z 1-Complex.I*fderiv ℝ (cutoffPotential m t) z Complex.I) := by
  have da := (modelRadial_derivatives t (log ‖z‖)).1
  have dy := (modelAngular_derivatives ht ht1 (upperAngle z)).1
  have dh := (polarProduct_hasFDerivAt hz hn da dy).const_mul (modelCoefficient m t)
  have eqn : cutoffPotential m t =ᶠ[𝓝 z] (fun w => modelCoefficient m t*polarProduct (modelRadial t) (modelAngular t) w) := by
    filter_upwards [eventually_ne_nhds hn] with w hw; simp [cutoffPotential,hw]
  have d := dh.congr_of_eventuallyEq eqn
  refine ⟨d.differentiableAt,?_⟩
  rw [cutoffField,if_neg hn,←polarProduct_field hz hn da dy,d.fderiv,(polarProduct_hasFDerivAt hz hn da dy).fderiv]
  simp only [smul_apply,smul_eq_mul]; ring

theorem cutoffField_equation (m : ℝ) {t : ℝ} (ht : 0<t) (ht1 : t<1) {z : ℂ} (hz : 0≤z.im) (hn : z≠0) :
    DifferentiableAt ℝ (cutoffField m t) z ∧ dbar (cutoffField m t) z=cutoffSource m t z := by
  obtain ⟨da,dda,_⟩ := modelRadial_derivatives t (log ‖z‖)
  obtain ⟨dy,ddy,_⟩ := modelAngular_derivatives ht ht1 (upperAngle z)
  obtain ⟨df,de⟩ := polarField_dbar hz hn da dda dy ddy
  have eqn : cutoffField m t =ᶠ[𝓝 z] (fun w => modelCoefficient m t*
      polarField (modelRadial t) (modelRadialD t) (modelAngular t) (modelAngularD t) w) := by
    filter_upwards [eventually_ne_nhds hn] with w hw; simp [cutoffField,hw]
  have d := (df.hasFDerivAt.const_mul (modelCoefficient m t)).congr_of_eventuallyEq eqn
  refine ⟨d.differentiableAt,?_⟩
  rw [cutoffSource,if_neg hn,←de,dbar,d.fderiv,dbar]
  simp only [smul_apply,smul_eq_mul]; ring

theorem cutoffSource_differentiable (m : ℝ) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    DifferentiableOn ℝ (cutoffSource m t) upper := by
  intro z hz
  have hn : z≠0 := fun he => by simpa [he,upper] using hz
  obtain ⟨da,_,dda⟩ := modelRadial_derivatives t (log ‖z‖)
  obtain ⟨dy,_,ddy⟩ := modelAngular_derivatives ht ht1 (upperAngle z)
  have h₁ := (polarProduct_hasFDerivAt (le_of_lt hz) hn dda.hasDerivAt dy).differentiableAt
  have h₂ := (polarProduct_hasFDerivAt (le_of_lt hz) hn da ddy.hasDerivAt).differentiableAt
  have hnorm := (differentiableAt_id (𝕜:=ℝ) (x:=z)).norm ℝ hn
  have hcast := Complex.ofRealCLM.differentiableAt.comp z hnorm
  let g := fun w : ℂ => modelCoefficient m t*(-(polarProduct (modelRadialDD t) (modelAngular t) w+
    polarProduct (modelRadial t) (modelAngularDD t) w)/(2*(‖w‖:ℂ)^2))
  have hd : DifferentiableAt ℝ g z := by
    have he : DifferentiableAt ℝ (fun w : ℂ => 2*(‖w‖:ℂ)^2) z := (hcast.pow 2).const_mul 2
    have hi := he.inv (show 2*(‖z‖:ℂ)^2≠0 by simp [hn])
    simpa only [g,div_eq_mul_inv,Pi.mul_def,Pi.neg_def,Pi.add_def,Pi.inv_def] using (((h₁.add h₂).neg.mul hi).const_mul (modelCoefficient m t))
  exact (hd.congr_of_eventuallyEq (by filter_upwards [eventually_ne_nhds hn] with w hw; simp [cutoffSource,hw,g])).differentiableWithinAt

theorem cutoffPotential_boundary (m : ℝ) {t : ℝ} (ht : 0<t) (ht1 : t<1) (x : ℝ) : cutoffPotential m t x=0 := by
  by_cases hx : x=0
  · simp [hx,cutoffPotential]
  have hn := Complex.ofReal_ne_zero.mpr hx
  obtain ⟨hy,hπ,_⟩ := angularSolution_dirichlet ht ht1
  rw [cutoffPotential,if_neg hn,polarProduct,upperAngle_eq (by simp) hn,modelAngular]
  rcases lt_or_gt_of_ne hx with h | h
  · simp [Complex.arg_ofReal_of_neg h,hπ]
  · simp [Complex.arg_ofReal_of_nonneg h.le,hy]

end Liu
