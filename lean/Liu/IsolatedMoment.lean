module

public import Liu.EdgeTraceEstimates
public import Liu.PoissonSemigroup
public import Liu.BoundaryL2

@[expose] public section

noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
namespace Liu

/-- A Poisson cutoff gives an integrable moment of the isolated trace. -/
theorem isolatedTrace_poisson_moment (a : ℝ) {b : ℝ} (hb : 0<b) :
    Integrable (fun x => poissonLine a 1 x*isolatedTrace a b x) ∧
    (∫ x, poissonLine a 1 x*isolatedTrace a b x)/π =
      ∫ t in Ioi b, 1/((t+b)*(1+t)) := by
  let μ := (volume:Measure ℝ).restrict (Ioi b)
  let k := fun t : ℝ => 1/((t+b)*(1+t))
  let P := fun t x : ℝ => poissonLine a 1 x*(poissonLine a t x/(t+b))
  have hk : Integrable k μ := by
    apply (integrableOn_Ioi_rpow_of_lt (a:=(-2:ℝ)) (by norm_num) hb).mono' ((show Measurable k by dsimp [k]; fun_prop).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with t ht
    have ht₀ := hb.trans ht
    have htb : 0<t+b := by positivity
    have ht₁ : 0<1+t := by positivity
    rw [Real.norm_of_nonneg (show 0≤k t by dsimp [k]; positivity),rpow_neg ht₀.le,rpow_ofNat,←one_div]
    apply one_div_le_one_div_of_le (sq_pos_of_pos ht₀)
    nlinarith only [ht₀,hb,mul_pos hb ht₀]
  have hP (t : ℝ) (ht : b<t) : (∫ x, P t x)=π*k t := by
    have ht₀ := hb.trans ht
    have he (x : ℝ) : P t x=(poissonLine a 1 x*poissonLine a t x)/(t+b) := by dsimp [P]; ring
    simp_rw [he,integral_div,poissonLine_pair_all a a zero_lt_one ht₀,sub_self]
    dsimp [k]; field_simp [show 1+t ≠ 0 by positivity,show t+b ≠ 0 by positivity] <;> ring
  have hK : Integrable (Function.uncurry P) (μ.prod volume) := by
    apply (integrable_prod_iff (show Measurable (Function.uncurry P) by dsimp [Function.uncurry,P,poissonLine]; fun_prop).aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with t ht
      apply Integrable.of_integral_ne_zero
      change (∫ x, P t x) ≠ 0
      rw [hP t ht]; dsimp [k]; have := hb.trans ht; positivity
    · apply (hk.const_mul π).congr
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))] with t ht
      rw [←hP t ht]
      apply integral_congr_ae
      filter_upwards with x
      have ht₀ := hb.trans ht
      exact (Real.norm_of_nonneg (show 0≤P t x by dsimp [P,poissonLine]; positivity)).symm
  have he (x : ℝ) : (∫ t, P t x ∂μ) = poissonLine a 1 x*isolatedTrace a b x := integral_const_mul ..
  refine ⟨hK.integral_prod_right.congr (ae_of_all _ he),?_⟩
  simp_rw [←he]
  rw [←integral_integral_swap hK]
  have eqn : (∫ t, ∫ x, P t x ∂volume ∂μ) = ∫ t, π*k t ∂μ :=
    integral_congr_ae ((ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))).mono hP)
  rw [eqn,integral_const_mul,mul_div_cancel_left₀ _ pi_ne_zero]

private theorem log_comparison_integral {b : ℝ} (hb : 0<b) :
    ∫ t in Ioi b, 1/(t*(1+t))=log (1+b⁻¹) := by
  let F := fun t : ℝ => -log (1+t⁻¹)
  have hd (t : ℝ) (ht : t∈Ici b) : HasDerivAt F (1/(t*(1+t))) t := by
    have ht₀ := hb.trans_le ht
    have hn : 1+t⁻¹≠0 := by positivity
    convert (((hasDerivAt_inv ht₀.ne').const_add 1).log hn).neg using 1
    field_simp [ht₀.ne',hn,show 1+t≠0 by positivity] <;> ring
  have hl : Tendsto F atTop (𝓝 0) := by
    have h := (continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp
      (show Tendsto (fun t : ℝ => 1+t⁻¹) atTop (𝓝 1) by simpa using (tendsto_inv_atTop_zero (𝕜:=ℝ)).const_add 1)
    simpa [F,Function.comp_def] using h.neg
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun t ht => by have := hb.trans ht; positivity) hl
  simpa [F] using h

/-- The Poisson moment of the unit shallow trace differs from log(1+1/b)
by at most one. This isolates the logarithmic coefficient. -/
theorem isolatedTrace_log_moment (a : ℝ) {b : ℝ} (hb : 0<b) :
    let J := (∫ x, poissonLine a 1 x*isolatedTrace a b x)/π
    log (1+b⁻¹)-1≤J ∧ J≤log (1+b⁻¹) := by
  rw [(isolatedTrace_poisson_moment a hb).2,←log_comparison_integral hb]
  let k := fun t : ℝ => 1/((t+b)*(1+t))
  let j := fun t : ℝ => 1/(t*(1+t))
  let μ := (volume:Measure ℝ).restrict (Ioi b)
  have hj : Integrable j μ := Integrable.of_integral_ne_zero ((log_comparison_integral hb) ▸ (log_pos (by have := inv_pos.mpr hb; linarith)).ne')
  have hT := (integrableOn_Ioi_rpow_of_lt (a:=(-2:ℝ)) (by norm_num) hb).const_mul b
  have hle (t : ℝ) (ht : b<t) : 0≤k t ∧ k t≤j t ∧ j t-k t≤b*t^(-(2:ℝ)) := by
    have ht₀ := hb.trans ht
    have htb : 0<t+b := by positivity
    have hp : 0<1+t := by positivity
    dsimp [k,j]
    refine ⟨by positivity,one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hp.le),?_⟩
    rw [rpow_neg ht₀.le,rpow_ofNat]
    field_simp [ht₀.ne',htb.ne',hp.ne']
    nlinarith only [mul_nonneg (sq_nonneg b) ht₀.le,mul_nonneg (sq_nonneg t) hb.le,
      mul_nonneg (sq_nonneg b) (sq_nonneg t),mul_nonneg (sq_nonneg b) zero_le_one]
  have hi : Integrable k μ := hj.mono' ((show Measurable k by dsimp [k]; fun_prop).aestronglyMeasurable) ((ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))).mono
    fun t ht => (Real.norm_of_nonneg (hle t ht).1).le.trans (hle t ht).2.1)
  constructor
  · have H := integral_mono_ae (hj.sub hi) hT ((ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))).mono
      (fun t ht => (hle t ht).2.2))
    change (∫ t, j t-k t ∂μ)≤∫ t in Ioi b, b*t^(-(2:ℝ)) at H
    rw [integral_sub hj hi,integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) hb] at H
    norm_num [rpow_neg_one,hb.ne'] at H
    change (∫ t, j t ∂μ)-1≤∫ t, k t ∂μ
    linarith
  · exact integral_mono_ae hi hj ((ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=b))).mono (fun t ht => (hle t ht).2.1))

end Liu
