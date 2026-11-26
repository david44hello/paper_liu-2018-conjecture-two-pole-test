import Liu.ModelFarField
import Liu.FieldComparison

noncomputable section
open Set MeasureTheory Real Filter Metric
open scoped Topology ComplexConjugate
namespace Liu

private theorem coeff_bound {m t : ℝ} (hm : 0 < m) (ht : t∈Icc (0:ℝ) 1) :
    ‖modelCoefficient m t‖ ≤ (max 1 m)^2 := by
  rw [norm_modelCoefficient hm]
  apply (rpow_le_rpow hm.le (le_max_right ..) (by linarith [ht.1] : 0≤1+t)).trans
  simpa only [rpow_ofNat] using rpow_le_rpow_of_exponent_le (le_max_left 1 m) (by linarith [ht.2] : 1+t≤(2:ℝ))

private theorem angular_dd_bound {t x : ℝ} (ht : 0<t) (ht1 : t<1) (hsmall : t*π≤1/2) (hx : x∈Icc 0 π) :
    ‖modelAngularDD t x‖ ≤ 2+8*π^2 := by
  obtain ⟨hy,_⟩ := angularSolution_uniform_bounds ht ht1 hsmall x hx
  apply (norm_sub_le ..).trans
  have hphase : ‖Complex.exp ((t:ℂ)*(x:ℂ)*Complex.I)‖=1 := by simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  simp only [norm_mul,Complex.norm_of_nonneg (by linarith : 0≤1+t),norm_pow,Complex.norm_of_nonneg ht.le,hphase,mul_one]
  exact add_le_add (by linarith) ((mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht.le ht1.le)).trans hy)

theorem cutoff_uniform_core_bounds {m R : ℝ} (hm : 0 < m) (hR : 1≤R) :
    ∃ C ≥ 0, ∀ t : ℝ, 0<t → t<1 → t*π≤1/2 → ∀ z : ℂ, 0≤z.im → ‖z‖≤R →
      ‖cutoffPotential m t z‖≤C ∧ ‖cutoffField m t z‖≤C ∧ ‖cutoffSource m t z‖≤C := by
  obtain ⟨B,hB,hb⟩ := modelRadial_uniform (log_nonneg hR)
  let M := (max 1 m)^2
  let Y := 2+8*π^2+8*π
  have hM : 0≤M := sq_nonneg _
  have hY : 0≤Y := by dsimp [Y]; positivity
  refine ⟨2*M*B*Y,by positivity,?_⟩
  intro t ht ht1 hsmall z hz hr
  by_cases small : ‖z‖<1
  · obtain ⟨a,b,c⟩ := cutoff_zero_on_ball m t small
    simp only [a,b,c,norm_zero,and_self]; positivity
  have hr1 := le_of_not_gt small
  have hrp := zero_lt_one.trans_le hr1
  have hn := norm_pos_iff.mp hrp
  have hθ : upperAngle z∈Icc 0 π := (upperAngle_eq hz hn) ▸ ⟨Complex.arg_nonneg_iff.mpr hz,Complex.arg_le_pi _⟩
  obtain ⟨hy,hv⟩ := angularSolution_uniform_bounds ht ht1 hsmall _ hθ
  have hdd := angular_dd_bound ht ht1 hsmall hθ
  have y : ‖modelAngular t (upperAngle z)‖≤Y := by dsimp [Y,modelAngular]; linarith [pi_pos]
  have v : ‖modelAngularD t (upperAngle z)‖≤Y := hv.trans (by dsimp [Y]; linarith [sq_nonneg π])
  have yy : ‖modelAngularDD t (upperAngle z)‖≤Y := by dsimp [Y]; linarith [pi_pos]
  obtain ⟨a,b,c⟩ := hb t ⟨ht.le,ht1.le⟩ _ (log_le_log hrp hr)
  have wgt := coeff_bound hm (show t∈Icc (0:ℝ) 1 from ⟨ht.le,ht1.le⟩)
  have hmul {A V : ℝ → ℂ} (hA : ‖A (log ‖z‖)‖≤B) (hV : ‖V (upperAngle z)‖≤Y) :
      ‖polarProduct A V z‖≤B*Y := by rw [polarProduct,norm_mul]; exact mul_le_mul hA hV (norm_nonneg _) hB
  have hi : ‖z⁻¹‖≤1 := by rw [norm_inv]; simpa using inv_anti₀ zero_lt_one hr1
  have hu : ‖polarProduct (modelRadial t) (modelAngular t) z‖≤B*Y+B*Y :=
    (hmul a y).trans (le_add_of_nonneg_right (by positivity))
  have hF : ‖polarField (modelRadial t) (modelRadialD t) (modelAngular t) (modelAngularD t) z‖≤B*Y+B*Y := by
    rw [polarField,norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) hi).trans
    apply (norm_add_le ..).trans
    simp only [norm_mul,norm_neg,Complex.norm_I,one_mul]
    exact add_le_add (hmul b y) (hmul a v)
  have hρ : ‖-(polarProduct (modelRadialDD t) (modelAngular t) z+polarProduct (modelRadial t) (modelAngularDD t) z)/(2*(‖z‖:ℂ)^2)‖≤B*Y+B*Y := by
    rw [norm_div,norm_neg,norm_mul,Complex.norm_two,norm_pow,Complex.norm_of_nonneg (norm_nonneg _)]
    apply (div_le_self (norm_nonneg _) (by nlinarith [one_le_pow₀ hr1 (n:=2)] : 1≤2*‖z‖^2)).trans
    exact (norm_add_le ..).trans (add_le_add (hmul c y) (hmul a yy))
  have scale (x : ℂ) (hx : ‖x‖≤B*Y+B*Y) : ‖modelCoefficient m t*x‖≤2*M*B*Y := by
    rw [norm_mul]; exact (mul_le_mul wgt hx (norm_nonneg _) hM).trans_eq (by ring)
  simp only [cutoffPotential,cutoffField,cutoffSource,if_neg hn]
  exact ⟨scale _ hu,scale _ hF,scale _ hρ⟩

theorem cutoff_continuous_closed (m : ℝ) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    ContinuousOn (cutoffPotential m t) {z : ℂ | 0≤z.im} ∧ ContinuousOn (cutoffField m t) {z : ℂ | 0≤z.im} := by
  have atzero : ∀ᶠ w in 𝓝 (0:ℂ), cutoffPotential m t w=0 ∧ cutoffField m t w=0 := by
    filter_upwards [ball_mem_nhds (0:ℂ) zero_lt_one] with w hw
    obtain ⟨a,b,_⟩ := cutoff_zero_on_ball m t (by simpa using hw)
    exact ⟨a,b⟩
  constructor <;> intro z hz
  · by_cases hn : z=0
    · subst z
      exact (continuousAt_const (y:=(0:ℂ)) |>.congr_of_eventuallyEq (atzero.mono fun _ h => h.1)).continuousWithinAt
    · exact (cutoffPotential_gradient m ht ht1 hz hn).1.continuousAt.continuousWithinAt
  · by_cases hn : z=0
    · subst z
      exact (continuousAt_const (y:=(0:ℂ)) |>.congr_of_eventuallyEq (atzero.mono fun _ h => h.2)).continuousWithinAt
    · exact (cutoffField_equation m ht ht1 hz hn).1.continuousAt.continuousWithinAt

end Liu
