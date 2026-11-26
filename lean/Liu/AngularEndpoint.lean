import Liu.AngularUniqueness

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

theorem angularSolution_zero (x : ℂ) :
    angularSolution 0 x = x*(x-(π:ℂ))/2 := if_pos rfl

theorem angularEnergy_zero : angularEnergy 0 = k₀ := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => angularSolution 0 t) ((x-π/2:ℝ):ℂ) x := by
    have d := (((hasDerivAt_id x).mul ((hasDerivAt_id x).sub_const π)).div_const 2).ofReal_comp
    convert d using 1
    · funext t; simp [angularSolution_zero]
    · push_cast; dsimp [id]; ring
  have he (x : ℝ) : ‖((0:ℝ):ℂ)*angularSolution 0 x+Complex.I*deriv (fun u : ℝ => angularSolution 0 u) x‖^2 =
      (π/2-x)^2 := by
    rw [(hd x).deriv]
    simp only [Complex.ofReal_zero,zero_mul,zero_add,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]; ring
  have hi : IntegrableOn (fun x : ℝ => (π/2-x)^2) (Ioo 0 π) :=
    (Continuous.integrableOn_Icc (by fun_prop : Continuous (fun x : ℝ => (π/2-x)^2))).mono_set Ioo_subset_Icc_self
  have h := angularDeficit_mean
  simp only [angularDeficit,integral_sub (integrableOn_const (C:=k₀) measure_Ioo_lt_top.ne) hi,
    setIntegral_const,smul_eq_mul,Real.volume_real_Ioo_of_le pi_pos.le,sub_zero] at h
  unfold angularEnergy
  simp_rw [he]
  rw [←sub_eq_zero.mp h]; field_simp [pi_ne_zero]

theorem angularEnergy_right_continuous :
    Tendsto angularEnergy (𝓝[>] 0) (𝓝 (angularEnergy 0)) := by
  rw [angularEnergy_zero]
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h := (angularEnergy_slope.mul (h0.const_mul 2)).add_const k₀
  simp only [mul_zero,zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
  change (angularEnergy t-k₀)/(2*t)*(2*t)+k₀=angularEnergy t
  rw [div_mul_cancel₀ _ (mul_ne_zero (by norm_num) (ne_of_gt ht)),sub_add_cancel]

theorem exterior_model_limit {m R : ℝ} (hm : 0 < m) (hR : 0<R) :
    Tendsto (fun t : ℝ => m^(2+2*t)*((angularEnergy t-k₀)/(2*t))*R^(-2*t))
      (𝓝[>] 0) (𝓝 (k₀*m^2)) := by
  have hmC : Continuous (fun t : ℝ => m^(2+2*t)) := by fun_prop (disch := exact hm.ne')
  have hRC : Continuous (fun t : ℝ => R^(-2*t)) := by fun_prop (disch := exact hR.ne')
  simpa [mul_comm k₀] using (((hmC.tendsto 0).mono_left nhdsWithin_le_nhds).mul angularEnergy_slope).mul
    ((hRC.tendsto 0).mono_left nhdsWithin_le_nhds)

end Liu
