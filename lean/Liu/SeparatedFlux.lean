import Liu.SeparatedSource

noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu.PickChart

def fluxIntegrand (P : PickChart) (w : ℂ) (x : ℝ) : ℂ :=
  P.trace w x * conj (P.trace (conj w) x) -
    (k₀:ℂ) * P.value w x * conj (P.value (conj w) x)

def fluxExtension (P : PickChart) (w : ℂ) : ℂ := (∫ x, P.fluxIntegrand w x)/(π:ℂ)

private theorem integrand_measurable (P : PickChart) (w : ℂ) : Measurable (P.fluxIntegrand w) := by
  let : SFinite upperArea := by unfold upperArea area; infer_instance
  have hT (v : ℂ) : Measurable (fun x : ℝ => P.trace v x) := by
    have hm : Measurable (fun p : ℝ × ℂ => ((p.2.im/‖p.2-(p.1:ℂ)‖^2:ℝ):ℂ)*P.rho v p.2) := by
      unfold rho valueFactor derivativeRatio nodeFactor; fun_prop
    exact (hm.stronglyMeasurable.integral_prod_right' (ν:=upperArea)).measurable
  unfold fluxIntegrand value valueFactor nodeFactor
  fun_prop

theorem Regular.flux_hasDeriv {P : PickChart} {U : Set ℂ} (h : P.Regular U) {c : ℂ} (hc : c∈U) :
    HasDerivAt P.fluxExtension ((∫ x : ℝ, deriv (fun w => P.fluxIntegrand w x) c)/(π:ℂ)) c := by
  apply HasDerivAt.div_const
  obtain ⟨K,hK,V,hV,hb⟩ := h.local_bounds hc
  let J := 2*K^7
  have hJ : 0≤J := by dsimp [J]; positivity
  have hk : 0≤k₀ := by unfold k₀; positivity
  refine hasDerivAt_local_integral volume h.isOpen hc (fun w => (integrand_measurable P w).aestronglyMeasurable)
    ?_ (M:=fun x => J^2*(isolatedTrace 0 1 x)^2 + (k₀*(K^3)^2)*‖linePole 0 1 x‖^2) ?_ hV ?_
  · filter_upwards with x
    have hT := h.trace_diff x
    have hS : DifferentiableOn ℂ (fun w => P.value w (x:ℂ)) U :=
      ((h.factors_diff (z:=(x:ℂ)) (by simp)).1.neg).div_const _
    exact (hT.mul (reflected_differentiable h.isOpen h.reflection hT)).sub
      ((hS.const_mul (k₀:ℂ)).mul (reflected_differentiable h.isOpen h.reflection hS))
  · have hIso := isolatedTrace_memLp 0 zero_lt_one
    have hi := (memLp_two_iff_integrable_sq hIso.aestronglyMeasurable).mp hIso
    exact (hi.const_mul _).add ((linePole_sq_integrable 0 zero_lt_one).const_mul _)
  · filter_upwards with x
    intro w hw
    obtain ⟨hu,hl,hr⟩ := hb w hw
    have hu' := h.reflection w hu
    have ht := h.trace_bound hu hl hr x
    have ht' := h.trace_bound hu' hr (by simpa using hl) x
    have hval {v : ℂ} (hv : v∈U) (hs : P.size v≤K) :
        ‖P.value v (x:ℂ)‖ ≤ K^3*‖linePole 0 1 x‖ := by
      have hs₀ : 0≤P.size v := (show (0:ℝ)≤1 by norm_num).trans (le_max_left ..)
      have hf := (factors_bounded h hv (z:=(x:ℂ)) (by simp)).1.trans (pow_le_pow_left₀ hs₀ hs 3)
      rw [value,norm_div,norm_neg]
      apply (div_le_div_of_nonneg_right hf (norm_nonneg _)).trans_eq
      simp [linePole,div_eq_mul_inv]
    have hI := isolatedTrace_nonneg 0 x zero_lt_one
    have h₁ := mul_le_mul ht ht' (norm_nonneg _) (mul_nonneg hJ hI)
    have h₂ := mul_le_mul (hval hu hl) (hval hu' hr) (norm_nonneg _) (mul_nonneg (pow_nonneg hK _) (norm_nonneg _))
    unfold fluxIntegrand
    apply (norm_sub_le ..).trans
    simp only [norm_mul,Complex.norm_conj,Complex.norm_of_nonneg hk]
    change ‖P.trace w x‖*‖P.trace (conj w) x‖+
      k₀*‖P.value w (x:ℂ)‖*‖P.value (conj w) (x:ℂ)‖≤_
    dsimp only [J] at *
    nlinarith only [h₁,mul_le_mul_of_nonneg_left h₂ hk]

theorem Regular.flux_analytic {P : PickChart} {U : Set ℂ} (h : P.Regular U) :
    AnalyticOnNhd ℂ P.fluxExtension U :=
  (show DifferentiableOn ℂ P.fluxExtension U from
    fun _ hc => (h.flux_hasDeriv hc).differentiableAt.differentiableWithinAt).analyticOnNhd h.isOpen

end Liu.PickChart
