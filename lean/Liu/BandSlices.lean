module

public import Liu.DepthStrip

@[expose] public section

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped Topology
namespace Liu

theorem integral_depthBand {f : ℂ → ℝ} {h : ℝ} (hh : 0≤h) (hi : IntegrableOn f (depthBand h) area) :
    (∫ z in depthBand h,f z ∂area)=(1/π)*(∫ y in (0:ℝ)..h, ∫ x : ℝ,f ⟨x,y⟩) := by
  classical
  have hM : MeasurableSet (depthBand h) := measurableSet_Ioc.preimage Complex.measurable_im
  have hs : depthBand h⊆upper := fun _ hz => hz.1
  have hI : Integrable ((depthBand h).indicator f) upperArea := ((integrable_indicator_iff hM).mpr hi).restrict
  have he := upperArea_slices _ hI
  rw [integral_indicator hM,upperArea,Measure.restrict_restrict hM,inter_eq_left.mpr hs] at he
  rw [he,smul_eq_mul,intervalIntegral.integral_of_le hh,←integral_indicator measurableSet_Ioc]
  congr 1
  rw [←integral_indicator measurableSet_Ioi]
  apply integral_congr_ae; filter_upwards with y
  by_cases hy : y∈Ioc (0:ℝ) h
  · rw [indicator_of_mem (show y∈Ioi (0:ℝ) from hy.1),indicator_of_mem hy]
    apply integral_congr_ae; filter_upwards with x
    exact indicator_of_mem (show (⟨x,y⟩:ℂ)∈depthBand h from hy) f
  · rw [indicator_of_notMem hy]
    by_cases hy' : y∈Ioi (0:ℝ)
    · rw [indicator_of_mem hy']; apply integral_eq_zero_of_ae
      exact ae_of_all _ (fun x => indicator_of_notMem (show (⟨x,y⟩:ℂ)∉depthBand h from hy) _)
    · rw [indicator_of_notMem hy']

private theorem plane_envelope_integrable {B : ℝ → ℝ} (hB : Integrable B) (h : ℝ) :
    Integrable (fun w : ℂ => B w.re*(Ioc (0:ℝ) h).indicator (fun _ => (1:ℝ)) w.im) volume := by
  let g := (Ioc (0:ℝ) h).indicator (fun _ => (1:ℝ))
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have hprod := hB.mul_prod hg
  have hv : Integrable (fun w : ℂ => B w.re*g w.im) volume := by
    simpa only [Function.comp_def,Complex.measurableEquivRealProd_apply,Measure.volume_eq_prod] using
      (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding).mpr hprod
  exact hv

theorem integrableOn_re_band {B : ℝ → ℝ} (hB : Integrable B) (h : ℝ) :
    IntegrableOn (fun z : ℂ => B z.re) (depthBand h) area := by
  have hv := ((plane_envelope_integrable hB h).smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).restrict (s:=depthBand h)
  exact hv.congr ((ae_restrict_mem (μ:=area) (show MeasurableSet (depthBand h) from measurableSet_Ioc.preimage Complex.measurable_im)).mono
    (fun w hw => by simp only [indicator_of_mem (show w.im∈Ioc 0 h from hw),mul_one]))

/-- An integrable horizontal envelope on a bounded band gives plane
integrability against the paper's normalized area. -/
theorem integrableOn_band_of_envelope {f : ℂ → ℝ} (hf : Measurable f) {B : ℝ → ℝ}
    (hB : Integrable B) {h : ℝ} (hp : ∀ z∈depthBand h, ‖f z‖≤B z.re) :
    IntegrableOn f (depthBand h) area := by
  have hv := plane_envelope_integrable hB h
  have hM : MeasurableSet (depthBand h) := measurableSet_Ioc.preimage Complex.measurable_im
  apply (integrable_indicator_iff (show MeasurableSet (depthBand h) from hM)).mp
  apply (hv.smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).mono' (hf.indicator hM).aestronglyMeasurable
  apply ae_of_all; intro w
  by_cases hw : w∈depthBand h
  · rw [indicator_of_mem hw,indicator_of_mem (show w.im∈Ioc 0 h from hw),mul_one]; exact hp w hw
  · rw [indicator_of_notMem hw,indicator_of_notMem (show w.im∉Ioc 0 h from hw),mul_zero,norm_zero]

end Liu
