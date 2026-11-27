module

public import Liu.ExteriorModel

@[expose] public section

noncomputable section
open Set Real
open scoped ComplexConjugate
namespace Liu

def modelAngularFlux (t x : ℝ) : ℂ := (t:ℂ)*modelAngular t x+Complex.I*modelAngularD t x

def exteriorField (m t : ℝ) (z : ℂ) : ℂ :=
  modelCoefficient m t*z⁻¹*((‖z‖^(-t):ℝ):ℂ)*modelAngularFlux t z.arg

theorem cutoffField_far (m t : ℝ) {z : ℂ} (hz : 0≤z.im) (hr : 2<‖z‖) :
    cutoffField m t z=exteriorField m t z := by
  have hp : 0<‖z‖ := by linarith
  have hn := norm_pos_iff.mp hp
  obtain ⟨h₀,h₁,_⟩ := modelRadial_far t (log_lt_log (by norm_num) hr)
  rw [cutoffField,if_neg hn,polarField,polarProduct,polarProduct,h₁,h₀,upperAngle_eq hz hn]
  dsimp only [exteriorField,modelAngularFlux]
  rw [rpow_def_of_pos hp,show log ‖z‖ * -t= -t*log ‖z‖ by ring]
  ring

private theorem exterior_phase {m t : ℝ} (hm : 0 < m) {z : ℂ} (hr : 0<‖z‖) :
    conj (Complex.exp (exteriorLog m z*(t:ℂ))) =
      ((m^t*‖z‖^(-t):ℝ):ℂ)*Complex.exp (-(t:ℂ)*(π:ℂ)*Complex.I)*Complex.exp ((t:ℂ)*(z.arg:ℂ)*Complex.I) := by
  rw [←Complex.exp_conj]
  simp only [exteriorLog,map_mul,map_add,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_mul]
  rw [rpow_def_of_pos hm,rpow_def_of_pos hr,Complex.ofReal_exp,Complex.ofReal_exp]
  rw [←Complex.exp_add,←Complex.exp_add,←Complex.exp_add]
  congr 1
  rw [Real.log_div hm.ne' hr.ne']
  push_cast; ring

theorem cutoffSource_far {m t : ℝ} (hm : 0 < m) {z : ℂ} (hz : 0≤z.im) (hr : 2<‖z‖) :
    cutoffSource m t z=exteriorFrozenSource m t z := by
  have hp : 0<‖z‖ := by linarith
  have hn := norm_pos_iff.mp hp
  obtain ⟨h₀,_,h₂⟩ := modelRadial_far t (log_lt_log (by norm_num) hr)
  rw [cutoffSource,if_neg hn,polarProduct,polarProduct,h₂,h₀,upperAngle_eq hz hn,exteriorFrozenSource,exterior_phase hm hp]
  dsimp only [modelCoefficient,modelAngularDD]
  rw [rpow_add hm,rpow_one,rpow_def_of_pos hp,show log ‖z‖ * -t= -t*log ‖z‖ by ring]
  push_cast; ring

theorem modelAngularFlux_bound {t x : ℝ} (ht : 0<t) (ht1 : t<1) (hsmall : t*π≤1/2) (hx : x∈Icc 0 π) :
    ‖modelAngularFlux t x‖≤8*π^2+8*π := by
  obtain ⟨hy,hv⟩ := angularSolution_uniform_bounds ht ht1 hsmall x hx
  apply (norm_add_le ..).trans
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_of_nonneg ht.le]
  exact add_le_add ((mul_le_of_le_one_left (norm_nonneg _) ht1.le).trans hy) hv

theorem exteriorField_norm {m : ℝ} (hm : 0 < m) (t : ℝ) (z : ℂ) :
    ‖exteriorField m t z‖=m^(1+t)*‖z‖⁻¹*‖z‖^(-t)*‖modelAngularFlux t z.arg‖ := by
  simp only [exteriorField,norm_mul,norm_modelCoefficient hm,norm_inv,Complex.norm_of_nonneg (rpow_nonneg (norm_nonneg _) _)]

end Liu
