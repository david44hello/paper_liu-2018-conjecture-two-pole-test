module

public import Liu.TraceKernel

@[expose] public section

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology ComplexConjugate
namespace Liu

private def traceWeight (v : ℂ) : ℝ := ‖v‖⁻¹/(1+‖v‖)^2

private theorem traceWeight_integrable : Integrable traceWeight area := by
  have h := integrable_one_add_norm (μ:=(volume:Measure ℂ)) (r:=(3:ℝ)) (by norm_num)
  have dom := (localInverse_integrable 0).add (h.const_mul 2)
  apply Integrable.smul_measure (μ:=volume) _ ENNReal.ofReal_ne_top
  apply dom.mono'
  · exact (show Measurable traceWeight by unfold traceWeight; fun_prop).aestronglyMeasurable
  filter_upwards with v
  change ‖traceWeight v‖ ≤ localInverse 0 v + 2*(1+‖v‖)^(-(3:ℝ))
  have hd : 0 < 1+‖v‖ := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [traceWeight]; positivity)]
  by_cases near : v ∈ Metric.ball (0:ℂ) 1
  · have hle : traceWeight v ≤ ‖v‖⁻¹ := div_le_self (by positivity) (by nlinarith [norm_nonneg v,sq_nonneg ‖v‖])
    simpa [localInverse,near] using hle.trans (le_add_of_nonneg_right
      (show 0 ≤ 2*(1+‖v‖)^(-(3:ℝ)) by positivity))
  · have hr : 1 ≤ ‖v‖ := by simpa using near
    have hv := zero_lt_one.trans_le hr
    simp only [localInverse,indicator_of_notMem near,zero_add,traceWeight,rpow_neg hd.le,rpow_ofNat]
    field_simp [hv.ne',hd.ne']
    <;> nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg (1+‖v‖))]

theorem translatedTrace_domination {ρ : ℂ → ℂ} {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hs : ∀ w : ℂ, 0 ≤ w.im → ‖ρ w‖ ≤ L/(1+‖w‖)^2)
    {z : ℂ} (hz : 0 < z.im) (hbound : ‖z‖ ≤ T) (v : ℂ) :
    ‖translatedTrace ρ z v‖ ≤ 2*L*(1+T)^2*(‖v‖⁻¹/(1+‖v‖)^2) := by
  by_cases hw : 0 < (z+v).im
  · have hk := greenLog_height_bound hz.le hw
    simp only [sub_add_cancel_left, norm_neg] at hk
    have hv : ‖v‖ ≤ ‖z+v‖+‖z‖ := by simpa using norm_sub_le (z+v) z
    have hscale : 1+‖v‖ ≤ (1+T)*(1+‖z+v‖) := by nlinarith [mul_nonneg hT (norm_nonneg (z+v))]
    have hsq := pow_le_pow_left₀ (show 0 ≤ 1+‖v‖ by positivity) hscale 2
    have dv : 0 < 1+‖v‖ := by positivity
    have dw : 0 < 1+‖z+v‖ := by positivity
    have hs' : L/(1+‖z+v‖)^2 ≤ (L*(1+T)^2)/(1+‖v‖)^2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos dw) (sq_pos_of_pos dv)).mpr
      rw [mul_pow] at hsq
      nlinarith [mul_le_mul_of_nonneg_left hsq hL]
    have hk' : |greenLog z (z+v)/z.im| ≤ 2*‖v‖⁻¹ := by
      rw [abs_div,abs_of_pos hz]
      apply (div_le_iff₀ hz).mpr
      simpa [mul_comm,mul_left_comm,mul_assoc] using hk
    simp only [translatedTrace,if_pos hw,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (2*‖v‖⁻¹)*((L*(1+T)^2)/(1+‖v‖)^2) :=
        mul_le_mul hk' ((hs _ hw.le).trans hs') (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · simp only [translatedTrace,if_neg hw,norm_zero]; positivity

theorem translatedTrace_integral_limit {ρ : ℂ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hm : Measurable ρ)
    (hc : ContinuousOn ρ {w : ℂ | 0 ≤ w.im})
    (hs : ∀ w : ℂ, 0 ≤ w.im → ‖ρ w‖ ≤ L/(1+‖w‖)^2) (x : ℝ) :
    Tendsto (fun z : ℂ => ∫ v, translatedTrace ρ z v ∂area) (𝓝[upper] (x:ℂ))
      (𝓝 (∫ v, boundaryTraceIntegrand ρ x v ∂area)) := by
  let T := ‖(x:ℂ)‖+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hb := traceWeight_integrable.const_mul (2*L*(1+T)^2)
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hb ?_
  · exact Eventually.of_forall fun z => (translatedTrace_measurable hm z).aestronglyMeasurable
  · have hid : Tendsto (fun z : ℂ => z) (𝓝[upper] (x:ℂ)) (𝓝 (x:ℂ)) := nhdsWithin_le_nhds
    have hr := (continuous_norm.continuousAt.tendsto.comp hid).eventually_lt_const
      (show ‖(x:ℂ)‖ < T by dsimp [T]; linarith)
    filter_upwards [self_mem_nhdsWithin (a := (x:ℂ)) (s := upper),hr] with z hz ht
    exact ae_of_all _ (translatedTrace_domination hL hT hs hz (le_of_lt ht))
  · exact ae_of_all _ (translatedTrace_limit x hc)

/-- The boundary integral used as the derivative is absolutely convergent. -/
theorem boundaryTrace_integrable {ρ : ℂ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hm : Measurable ρ)
    (hc : ContinuousOn ρ {w : ℂ | 0 ≤ w.im}) (hs : ∀ w : ℂ, 0 ≤ w.im → ‖ρ w‖ ≤ L/(1+‖w‖)^2) (x : ℝ) :
    Integrable (boundaryTraceIntegrand ρ x) area := by
  let T := ‖(x:ℂ)‖+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have path : Tendsto (fun y : ℝ => (x:ℂ)+(y:ℂ)*Complex.I) (𝓝[>] 0) (𝓝[upper] (x:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : Continuous (fun y : ℝ => (x:ℂ)+(y:ℂ)*Complex.I) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with y hy
      simpa [upper] using hy
  have hb := traceWeight_integrable.const_mul (2*L*(1+T)^2)
  apply hb.mono'
  · have hm' : Measurable (boundaryTraceIntegrand ρ x) := by
      unfold boundaryTraceIntegrand
      apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop) measurable_const
    exact hm'.aestronglyMeasurable
  filter_upwards with v
  apply le_of_tendsto (((translatedTrace_limit x hc v).comp path).norm)
  have hnorm := (continuous_norm.continuousAt.tendsto.comp (path.mono_right nhdsWithin_le_nhds)).eventually_lt_const
    (show ‖(x:ℂ)‖ < T by dsimp [T]; linarith)
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),hnorm] with y hy hh
  exact translatedTrace_domination hL hT hs (by simpa using hy : 0 < ((x:ℂ)+(y:ℂ)*Complex.I).im) hh.le v

theorem PickSum.source_continuousOn {n : ℕ} (p : PickSum n) :
    ContinuousOn (source p.value) {w : ℂ | 0 ≤ w.im} := by
  let K := {w : ℂ | 0 ≤ w.im}
  have hc : ContinuousOn p.value K := fun w hw => (p.hasDerivAt hw).continuousAt.continuousWithinAt
  have hd : ContinuousOn (deriv p.value) K := by
    apply ContinuousOn.congr (f:=fun w => ∑ i, (p.weight i:ℂ)/(w-p.location i)^2) _
      (fun w hw => (p.hasDerivAt hw).deriv)
    apply continuousOn_finset_sum
    intro i _
    apply continuousOn_const.div (by fun_prop)
    intro w hw
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro eqn
    have hh : 0 ≤ w.im := hw
    rw [eqn] at hh
    linarith [p.below i]
  have hnc (w : ℂ) (hw : w ∈ K) : conj (p.value w) ≠ 0 := by
    have hn : p.value w ≠ 0 := fun he => by have hi := p.value_im_pos hw; simp [he] at hi
    simpa using hn
  unfold source
  exact (continuousOn_const.mul (hc.div (Complex.continuous_conj.comp_continuousOn hc) hnc)).mul
    (Complex.continuous_conj.comp_continuousOn hd)

private theorem add_preserves_area (z : ℂ) : MeasurePreserving (fun v : ℂ => z+v) area area := by
  have h := measurePreserving_add_left (volume:Measure ℂ) z
  exact ⟨h.measurable,by unfold area; rw [Measure.map_smul _ h.measurable.aemeasurable,h.map_eq]⟩

theorem potential_div_height (S : ℂ → ℂ) (z : ℂ) :
    potential S z/(z.im:ℂ) = ∫ v, translatedTrace (source S) z v ∂area := by
  classical
  rw [potential,←integral_div]
  rw [←integral_indicator upper_open.measurableSet]
  rw [← (add_preserves_area z).integral_comp (Homeomorph.addLeft z).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with v
  by_cases h : 0 < (z+v).im
  · simp only [indicator_of_mem (show z+v ∈ upper from h),translatedTrace,if_pos h,Complex.ofReal_div,greenLog]
    ring
  · simp only [indicator_of_notMem (show z+v ∉ upper from h),translatedTrace,if_neg h]

theorem PickSum.potential_normal_quotient {n : ℕ} (p : PickSum n) (x : ℝ) :
    Tendsto (fun z : ℂ => potential p.value z/(z.im:ℂ)) (𝓝[upper] (x:ℂ))
      (𝓝 (∫ v, boundaryTraceIntegrand (source p.value) x v ∂area)) := by
  simp only [potential_div_height]
  apply translatedTrace_integral_limit (L:=p.derivativeBound/2) _ p.source_measurable p.source_continuousOn
    (fun _ hz => p.source_decay hz)
  simpa using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))

end Liu
