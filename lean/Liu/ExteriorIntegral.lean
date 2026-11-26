import Liu.ExteriorEnergyError

noncomputable section
open Set MeasureTheory Filter Real Metric
open scoped Topology
namespace Liu

private theorem integral_upper_ball (f : ℂ → ℝ) (R : ℝ) :
    (∫ z in ball (0:ℂ) R, f z ∂upperArea) = ∫ z in halfDisc R, f z ∂area := by
  rw [upperArea,Measure.restrict_restrict isOpen_ball.measurableSet,inter_comm,halfDisc]

theorem PickSum.frozen_density_integral {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    Integrable (p.frozenDensity t) upperArea ∧
    (∫ z, p.frozenDensity t z ∂upperArea) =
    energy (canonicalField (p.frozenLogSource t))-k₀*energy (p.power (1+t)) := by
  have h := (p.supercritical_sources ht ht1).2.field_memLp
  have g := p.power_memLp_two (show 1<1+t by linarith)
  have hi := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  have hj := (memLp_two_iff_integrable_sq_norm g.aestronglyMeasurable).mp g
  refine ⟨hi.sub (hj.const_mul k₀),?_⟩
  unfold PickSum.frozenDensity
  rw [energy_eq_integral h,energy_eq_integral g,integral_sub hi (hj.const_mul k₀),integral_const_mul]

private theorem modelDensity_measurable (m : ℝ) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    Measurable (modelEnergyDensity m t) := by
  have hy : Continuous (modelAngular t) := continuous_iff_continuousAt.mpr (fun x => (modelAngular_derivatives ht ht1 x).1.continuousAt)
  have hv : Continuous (modelAngularD t) := continuous_iff_continuousAt.mpr (fun x => (modelAngular_derivatives ht ht1 x).2.1.continuousAt)
  have hf : Continuous (modelAngularFlux t) := by unfold modelAngularFlux; fun_prop
  have ha := hf.measurable.comp Complex.measurable_arg
  unfold modelEnergyDensity
  fun_prop

/-- The physical integral differs from the sum of the bounded part and the explicit
exterior model by at most an integrable tail, uniformly in the small exponent. -/
theorem PickSum.frozen_integral_approximation {n : ℕ} (p : PickSum n) :
    ∃ L ≥ 0, ∀ R : ℝ, 3≤R → ∀ t : ℝ, 0<t → t<1 → t*π≤1/2 →
    |(∫ z, p.frozenDensity t z ∂upperArea) -
      ((∫ z in halfDisc R, p.frozenDensity t z ∂area) +
        p.mass^(2+2*t)*((angularEnergy t-k₀)/(2*t))*R^(-2*t))| ≤
      L*((∫ z, logTail z ∂upperArea)-(∫ z in halfDisc R, logTail z ∂area)) := by
  classical
  obtain ⟨L,hL,he⟩ := p.frozen_energy_tail_error
  refine ⟨L,hL,?_⟩
  intro R hR t ht ht1 hs
  let D := ball (0:ℂ) R
  let f := p.frozenDensity t
  let g := modelEnergyDensity p.mass t
  have hD : MeasurableSet D := isOpen_ball.measurableSet
  have hi : Integrable f upperArea := (p.frozen_density_integral ht ht1).1
  have hd := integral_add_compl hD hi
  have hl := integral_add_compl hD logTail_integrable
  have htail : (∫ z in Dᶜ, logTail z ∂upperArea)=(∫ z, logTail z ∂upperArea)-(∫ z in halfDisc R, logTail z ∂area) := by
    rw [←integral_upper_ball]; linarith only [hl]
  let μ := upperArea.restrict Dᶜ
  have hu : ∀ᵐ z ∂μ, z∈upper := ae_mono Measure.restrict_le_self (ae_restrict_mem (μ:=area) upper_open.measurableSet)
  have hpt : ∀ᵐ z ∂μ, ‖f z-g z‖≤L*logTail z := by
    filter_upwards [hu,ae_restrict_mem (μ:=upperArea) hD.compl] with z hz hzD
    have hr : R≤‖z‖ := by simpa [D] using hzD
    exact he t ht ht1 hs z (le_of_lt hz) (by linarith)
  have hi' : Integrable f μ := hi.restrict
  have hj := (show Integrable logTail μ from logTail_integrable.restrict).const_mul L
  have herr : Integrable (fun z => f z-g z) μ :=
    hj.mono' (hi'.aestronglyMeasurable.sub (modelDensity_measurable p.mass ht ht1).aestronglyMeasurable) hpt
  have hg : Integrable g μ := (hi'.sub herr).congr (ae_of_all _ (fun z => by simp [Pi.sub_apply]))
  have hbound := norm_integral_le_of_norm_le hj hpt
  rw [integral_sub hi' hg,Real.norm_eq_abs,integral_const_mul] at hbound
  have hmodel := exterior_model_energy_integral p.mass ht ht1 (show 0<R by linarith)
  have hcut : Dᶜ.indicator g = fun z => if R≤‖z‖ then modelEnergyDensity p.mass t z else 0 := by
    funext z; by_cases h : R≤‖z‖
    · rw [indicator_of_mem (show z∈Dᶜ by simpa [D] using h),if_pos h]
    · rw [indicator_of_notMem (show z∉Dᶜ by simpa [D] using h),if_neg h]
  rw [←hcut,integral_indicator hD.compl] at hmodel
  rw [←hmodel,←integral_upper_ball]
  change |(∫ z, f z ∂upperArea)-((∫ z in D, f z ∂upperArea)+(∫ z, g z ∂μ))|≤_
  rw [←hd,add_sub_add_left_eq_sub,←htail]
  exact hbound

end Liu
