import Liu.ModelFarField
import Liu.AngularDeficit

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology
namespace Liu

def modelEnergyDensity (m t : ℝ) (z : ℂ) :=
  m^(2+2*t)*‖z‖^(-(2+2*t))*(‖modelAngularFlux t z.arg‖^2-k₀)

theorem exteriorField_sq {m : ℝ} (hm : 0 < m) (t : ℝ) {z : ℂ} (hz : z≠0) :
    ‖exteriorField m t z‖^2=m^(2+2*t)*‖z‖^(-(2+2*t))*‖modelAngularFlux t z.arg‖^2 := by
  have hr := norm_pos_iff.mpr hz
  rw [exteriorField_norm hm]
  have hm' : (m^(1+t))^2=m^(2+2*t) := by rw [←rpow_ofNat (m^(1+t)) 2,←rpow_mul hm.le]; congr 1; ring
  have hr' : ‖z‖⁻¹*‖z‖^(-t)=‖z‖^(-1-t) := by rw [sub_eq_add_neg,rpow_add hr,rpow_neg_one]
  have hr'' : (‖z‖^(-1-t))^2=‖z‖^(-(2+2*t)) := by rw [←rpow_ofNat (‖z‖^(-1-t)) 2,←rpow_mul hr.le]; congr 1; ring
  rw [mul_assoc (m^(1+t)),hr',mul_pow,mul_pow,hm',hr'']

private theorem radialExterior_integral {q R : ℝ} (hq : 2<q) (hR : 0<R) :
    (∫ z : ℂ, (if R≤‖z‖ then ‖z‖^(-q) else 0) ∂upperArea)=R^(2-q)/(q-2) := by
  rw [upperArea_radial (fun r => if R≤r then r^(-q) else 0)]
  calc
    _ = ∫ r in Ioi (0:ℝ), (Ici R).indicator (fun u => u^(1-q)) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      by_cases h : R≤r
      · simp only [if_pos h,indicator_of_mem (show r∈Ici R from h)]
        rw [sub_eq_add_neg,rpow_add hr,rpow_one]
      · simp [h,indicator_of_notMem (show r∉Ici R from h)]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Ici,inter_eq_right.mpr (show Ici R⊆Ioi 0 from fun r hr => hR.trans_le hr),
        integral_Ici_eq_integral_Ioi,integral_Ioi_rpow_of_lt (by linarith) hR]
      rw [show 1-q+1=2-q by ring,show 2-q=-(q-2) by ring,neg_div_neg_eq]

theorem exterior_model_energy_integral (m : ℝ) {t R : ℝ} (ht : 0<t) (ht1 : t<1) (hR : 0<R) :
    (∫ z : ℂ, (if R≤‖z‖ then modelEnergyDensity m t z else 0) ∂upperArea) =
      m^(2+2*t)*((angularEnergy t-k₀)/(2*t))*R^(-2*t) := by
  let q := 2+2*t
  let a := fun x => ‖modelAngularFlux t x‖^2
  have ha : Continuous a := by
    have dy : Continuous (modelAngular t) := continuous_iff_continuousAt.mpr (fun x => (modelAngular_derivatives ht ht1 x).1.continuousAt)
    have dv : Continuous (modelAngularD t) := continuous_iff_continuousAt.mpr (fun x => (modelAngular_derivatives ht ht1 x).2.1.continuousAt)
    dsimp [a,modelAngularFlux]; fun_prop
  have hi : IntegrableOn a (Ioo (0:ℝ) π) volume := (ha.integrableOn_Icc (a:=0) (b:=π)).mono_set Ioo_subset_Icc_self
  have hk := integrableOn_const (s:=Ioo (0:ℝ) π) (μ:=volume) (C:=k₀) measure_Ioo_lt_top.ne
  have hang : (1/π)*∫ x in Ioo (0:ℝ) π, a x-k₀ = angularEnergy t-k₀ := by
    rw [integral_sub hi hk,setIntegral_const,Real.volume_real_Ioo_of_le pi_pos.le,smul_eq_mul,sub_zero]
    change _=(1/π)*(∫ x in Ioo (0:ℝ) π, a x)-k₀
    field_simp [pi_ne_zero]
  have he (z : ℂ) : (if R≤‖z‖ then modelEnergyDensity m t z else 0) =
      m^q*((if R≤‖z‖ then ‖z‖^(-q) else 0)*(a z.arg-k₀)) := by
    dsimp [modelEnergyDensity,a,q]; split <;> ring
  simp_rw [he]
  rw [integral_const_mul,upperArea_separated (fun r => if R≤r then r^(-q) else 0) (fun x => a x-k₀),hang,
    radialExterior_integral (show 2<q by dsimp [q]; linarith) hR]
  dsimp only [q]
  rw [show 2-(2+2*t)= -2*t by ring,show 2+2*t-2=2*t by ring]
  ring

end Liu
