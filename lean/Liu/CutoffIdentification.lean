module

public import Liu.ModelBounds

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter Metric
open scoped ComplexConjugate Topology
namespace Liu

private theorem cutoff_field_global_bound {m t : ℝ} (hm : 0 < m) (ht : 0<t) (ht1 : t<1) (hsmall : t*π≤1/2) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → ‖cutoffField m t z‖≤C/(1+‖z‖)^(1+t) := by
  obtain ⟨A,hA,ha⟩ := cutoff_uniform_core_bounds hm (R:=2) (by norm_num)
  let Y := 8*π^2+8*π
  let M := m^(1+t)
  have hY : 0≤Y := by dsimp [Y]; positivity
  have hM : 0≤M := rpow_nonneg hm.le _
  let C := A*(3:ℝ)^(1+t)+M*Y*(2:ℝ)^(1+t)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro z hz
  apply (le_div_iff₀ (rpow_pos_of_pos (by positivity) _)).mpr
  by_cases hr : ‖z‖≤2
  · have hh := (ha t ht ht1 hsmall z hz hr).2.1
    exact (mul_le_mul hh (rpow_le_rpow (by positivity) (by linarith : 1+‖z‖≤3) (by linarith)) (by positivity) hA).trans (le_add_of_nonneg_right (by positivity))
  · have h2 := lt_of_not_ge hr
    have hp : 0<‖z‖ := by linarith
    rw [cutoffField_far m t hz h2,exteriorField_norm hm]
    have hflux := modelAngularFlux_bound ht ht1 hsmall (show z.arg ∈ Icc 0 π from ⟨Complex.arg_nonneg_iff.mpr hz,Complex.arg_le_pi _⟩)
    have hscale := rpow_le_rpow (by positivity : 0≤1+‖z‖) (by linarith : 1+‖z‖≤2*‖z‖) (by linarith : 0≤1+t)
    rw [mul_rpow (by norm_num) hp.le,rpow_add hp,rpow_one] at hscale
    change M*‖z‖⁻¹*‖z‖^(-t)*‖modelAngularFlux t z.arg‖*(1+‖z‖)^(1+t)≤_
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hflux (by positivity : 0≤M*‖z‖⁻¹*‖z‖^(-t))) hscale (by positivity) (by positivity)).trans
    rw [rpow_neg hp.le]
    have eqn : M*‖z‖⁻¹*(‖z‖^t)⁻¹*Y*(2^(1+t)*(‖z‖*‖z‖^t))=M*Y*2^(1+t) := by
      field_simp [hp.ne',(rpow_pos_of_pos hp t).ne']
    exact eqn.le.trans (le_add_of_nonneg_left (by positivity))

theorem cutoffField_projection {m t : ℝ} (hm : 0 < m) (ht : 0<t) (ht1 : t<1) (hsmall : t*π≤1/2) :
    MemLp (cutoffField m t) 2 upperArea ∧ project (asL2 (cutoffField m t))=0 := by
  obtain ⟨Cu,Cf⟩ := cutoff_continuous_closed m ht ht1
  obtain ⟨C,_,hb⟩ := cutoff_field_global_bound hm ht ht1 hsmall
  have hL := memLp_two_of_power_bound ht ((Cf.mono (show upper ⊆ {z : ℂ | 0≤z.im} from fun z hz => (show 0<z.im from hz).le)).aestronglyMeasurable upper_open.measurableSet)
    (fun z hz => hb z (le_of_lt hz))
  obtain ⟨B,hB,hc⟩ := cutoff_uniform_core_bounds hm (R:=2) (by norm_num)
  have bound (z : ℂ) (hz : 0≤z.im) : ‖cutoffPotential m t z‖≤B+m^(1+t)*(8*π^2) := by
    by_cases hr : ‖z‖≤2
    · exact (hc t ht ht1 hsmall z hz hr).1.trans (le_add_of_nonneg_right (by positivity))
    have hp : 0<‖z‖ := by linarith [lt_of_not_ge hr]
    have hn := norm_pos_iff.mp hp
    have hl := log_lt_log (by norm_num : (0:ℝ)<2) (lt_of_not_ge hr)
    have hθ : z.arg∈Icc 0 π := ⟨Complex.arg_nonneg_iff.mpr hz,Complex.arg_le_pi _⟩
    have he : exp (-t*log ‖z‖)≤1 := exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (log_nonneg (by linarith [lt_of_not_ge hr])))
    rw [cutoffPotential,if_neg hn,norm_mul,norm_modelCoefficient hm,polarProduct,norm_mul,(modelRadial_far t hl).1,
       Complex.norm_of_nonneg (exp_pos _).le,upperAngle_eq hz hn]
    apply (mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (norm_nonneg _) he).trans (angularSolution_uniform_bounds ht ht1 hsmall _ hθ).1) (rpow_nonneg hm.le _)).trans
    exact le_add_of_nonneg_left hB
  have hp (z : ℂ) (hz : z∈upper) := cutoffPotential_gradient m ht ht1 (le_of_lt hz) (show z≠0 from fun he => by simpa [he,upper] using hz)
  exact ⟨hL,dirichlet_field_projection_zero Cu (fun z hz => (hp z hz).1.hasFDerivAt) (fun z hz => (hp z hz).2)
    (cutoffPotential_boundary m ht ht1) (by positivity) bound hL⟩

end Liu
