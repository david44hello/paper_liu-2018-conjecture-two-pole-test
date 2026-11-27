module

public import Liu.RadialEnergy
public import Liu.Potential

@[expose] public section

noncomputable section
open Set MeasureTheory Real Metric
namespace Liu

def momentDisc (T : ℝ) (w : ℂ) : ℝ :=
  if ‖w‖ ≤ T then ‖w‖⁻¹/(1+‖w‖) else 0

def exteriorFourth (T : ℝ) (w : ℂ) : ℝ :=
  if T < ‖w‖ then (‖w‖^4)⁻¹ else 0

theorem momentDisc_integral {T : ℝ} (hT : 0<T) :
    Integrable (momentDisc T) upperArea ∧ (∫ w, momentDisc T w ∂upperArea) = log (1+T) := by
  have hm : Measurable (momentDisc T) := by
    unfold momentDisc; exact Measurable.ite (measurableSet_le measurable_norm measurable_const) (by fun_prop) measurable_const
  have hcore := (integrable_indicator_iff (Metric.isOpen_ball (x:=(0:ℂ)) (ε:=T+1)).measurableSet).mpr
    (integrable_inverse_distance_ball (T+1))
  have hv : Integrable (momentDisc T) volume := by
    apply hcore.mono' hm.aestronglyMeasurable
    filter_upwards with w
    by_cases hw : ‖w‖≤T
    · have hmem : w∈ball (0:ℂ) (T+1) := by simpa using (by linarith : ‖w‖<T+1)
      rw [momentDisc,if_pos hw,indicator_of_mem hmem,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤‖w‖⁻¹/(1+‖w‖))]
      exact div_le_self (by positivity) (by linarith [norm_nonneg w])
    · rw [momentDisc,if_neg hw,norm_zero]
      apply indicator_nonneg; exact fun _ _ => by positivity
  refine ⟨(hv.smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).restrict,?_⟩
  unfold momentDisc
  rw [upperArea_radial (fun r => if r≤T then r⁻¹/(1+r) else 0)]
  have he (r : ℝ) (hr : r∈Ioi (0:ℝ)) :
      r*(if r≤T then r⁻¹/(1+r) else 0) = (Ioc (0:ℝ) T).indicator (fun x => (1+x)⁻¹) r := by
    by_cases hrT : r≤T
    · rw [if_pos hrT,indicator_of_mem (show r ∈ Ioc _ _ from ⟨hr,hrT⟩)]
      rw [←mul_div_assoc,mul_inv_cancel₀ (ne_of_gt hr),one_div]
    · simp [hrT,show r∉Ioc (0:ℝ) T from fun e => hrT e.2]
  rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr Ioc_subset_Ioi_self,←intervalIntegral.integral_of_le hT.le]
  have hd (x : ℝ) (hx : x∈Set.uIcc 0 T) : HasDerivAt (fun r : ℝ => log (1+r)) (1+x)⁻¹ x := by
    rw [uIcc_of_le hT.le] at hx
    simpa [one_div] using ((hasDerivAt_id x).const_add 1).log (by linarith [hx.1] : 1+x≠0)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply ContinuousOn.intervalIntegrable
    intro r hr
    rw [uIcc_of_le hT.le] at hr
    fun_prop (disch := linarith [hr.1]))]
  simp

theorem exteriorFourth_integral {T : ℝ} (hT : 0<T) :
    Integrable (exteriorFourth T) upperArea ∧ (∫ w, exteriorFourth T w ∂upperArea) = 1/(2*T^2) := by
  have hm : Measurable (exteriorFourth T) := by
    unfold exteriorFourth; exact Measurable.ite (measurableSet_lt measurable_const measurable_norm) (by fun_prop) measurable_const
  have hi := (integrable_one_add_norm (r:=4) (μ:=(volume:Measure ℂ)) (by norm_num)).const_mul ((1+T⁻¹)^4)
  have hv : Integrable (exteriorFourth T) volume := by
    apply hi.mono' hm.aestronglyMeasurable
    filter_upwards with w
    by_cases hw : T<‖w‖
    · rw [exteriorFourth,if_pos hw,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(‖w‖^4)⁻¹)]
      simp only [rpow_neg (by positivity : 0≤1+‖w‖),rpow_ofNat]
      have h1 : 1 ≤ T⁻¹*‖w‖ := by rw [inv_mul_eq_div]; exact (one_le_div hT).mpr hw.le
      have hp := pow_le_pow_left₀ (by positivity : 0≤1+‖w‖) (by linarith : 1+‖w‖≤(1+T⁻¹)*‖w‖) 4
      rw [mul_pow] at hp
      change (‖w‖^4)⁻¹ ≤ (1+T⁻¹)^4*((1+‖w‖)^4)⁻¹
      rw [←one_div,←div_eq_mul_inv]
      apply (div_le_div_iff₀ (pow_pos (hT.trans hw) 4) (by positivity)).mpr
      simpa only [one_mul] using hp
    · simp only [exteriorFourth,if_neg hw,norm_zero]
      positivity
  refine ⟨(hv.smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).restrict,?_⟩
  unfold exteriorFourth
  rw [upperArea_radial (fun r => if T<r then (r^4)⁻¹ else 0)]
  have he (r : ℝ) (hr : r∈Ioi (0:ℝ)) : r*(if T<r then (r^4)⁻¹ else 0) =
      (Ioi T).indicator (fun u : ℝ => u^(-(3:ℝ))) r := by
    by_cases ht : T<r
    · rw [if_pos ht,indicator_of_mem (show r ∈ Ioi T from ht),rpow_neg (le_of_lt hr),rpow_ofNat]
      field_simp [(ne_of_gt (show 0<r from hr))]
    · simp [ht,show r∉Ioi T from ht]
  rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi hT.le),integral_Ioi_rpow_of_lt (by norm_num) hT]
  norm_num
  ring

end Liu
