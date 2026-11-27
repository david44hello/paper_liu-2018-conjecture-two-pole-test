module

public import Liu.WeakApproximation

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Real Metric
open scoped Topology ENNReal
namespace Liu

private theorem upper_le_volume : upperArea≤(volume:Measure ℂ) := by
  refine Measure.restrict_le_self.trans ?_
  change (ENNReal.ofReal (1/π)) • (volume:Measure ℂ) ≤ volume
  have hc : ENNReal.ofReal (1/π)≤1 := by
    rw [ENNReal.ofReal_le_one]; exact (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  calc
    _ ≤ (1:ℝ≥0∞) • (volume:Measure ℂ) := by gcongr
    _ = _ := one_smul .. 

private theorem zero_extension {h : ℂ → ℂ} (hh : MemLp h 2 upperArea) (hw : WeakDbar h 0) :
    ∃ f : ℂ → ℂ, Measurable f ∧ MemLp f 2 volume ∧ upperWeakZero f ∧ f=ᵐ[upperArea] h := by
  let c := ENNReal.ofReal (1/π)
  have hc : c≠0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hs : upperArea=c • (volume:Measure ℂ).restrict upper := by rw [upperArea,area,Measure.restrict_smul]
  have hr := hh.smul_measure (c:=c⁻¹) (by simpa using hc)
  rw [hs,smul_smul,ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top,one_smul] at hr
  let E := upper.indicator h
  have hE : MemLp E 2 volume := (memLp_indicator_iff_restrict upper_open.measurableSet.nullMeasurableSet).mpr hr
  let f := hE.aestronglyMeasurable.mk E
  have he : E=ᵐ[volume] f := hE.aestronglyMeasurable.ae_eq_mk
  refine ⟨f,hE.aestronglyMeasurable.measurable_mk,hE.ae_eq he,?_,?_⟩
  · intro φ dφ hcmp hsub
    have H := hw φ dφ hcmp hsub
    simp only [Pi.zero_apply,zero_mul,integral_zero,neg_zero] at H
    rw [hs,integral_smul_measure,smul_eq_zero] at H
    have hc' : c.toReal≠0 := ENNReal.toReal_ne_zero.mpr ⟨hc,ENNReal.ofReal_ne_top⟩
    have hI := H.resolve_left hc'
    calc
      _ = ∫ w, upper.indicator (fun w => h w*dbar φ w) w := by
        apply integral_congr_ae; filter_upwards [he] with w he
        rw [←he]; by_cases h : w∈upper <;> simp [E,h]
      _ = _ := (integral_indicator upper_open.measurableSet).trans hI
  · filter_upwards [he.filter_mono (ae_mono upper_le_volume),ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz hu
    simpa [E,hu] using hz.symm

/-- Distributional Weyl lemma for L² in the upper half-plane, with an actual
holomorphic representative obtained by closure of the analytic subspace. -/
theorem weak_holomorphic_mem_analytic {h : ℂ → ℂ} (hh : MemLp h 2 upperArea) (hw : WeakDbar h 0) :
    hh.toLp h∈analyticVectors := by
  obtain ⟨f,hfm,hf,hw,he⟩ := zero_extension hh hw
  have hfU := hf.mono_measure upper_le_volume
  rw [←hfU.toLp_congr hh he,←analyticVectors_closed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g,dg,hg,hb⟩ := weak_analytic_approximation hfm hf hw (show 0<ε/2 by linarith)
  have hgU := hg.mono_measure upper_le_volume
  refine ⟨hgU.toLp g,⟨g,hgU,dg,rfl⟩,?_⟩
  have ht := (hg.sub hf)
  have hi := (memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable).mp ht
  have hle := integral_mono_measure upper_le_volume (ae_of_all _ fun z => sq_nonneg ‖g z-f z‖) hi
  have hsq := lp_two_integral_sq (hgU.sub hfU)
  rw [MemLp.toLp_sub hgU hfU] at hsq
  change (∫ z, ‖g z-f z‖^2 ∂upperArea)=_ at hsq
  have H := hsq.symm.trans_le (hle.trans hb)
  rw [dist_comm,dist_eq_norm]
  exact (le_of_sq_le_sq H (by linarith)).trans_lt (by linarith)

theorem SupercriticalSource.weak_residual_eq_field {f h : ℂ → ℂ} {t : ℝ} (hf : SupercriticalSource f t)
    (df : DifferentiableOn ℝ f upper) (hh : MemLp h 2 upperArea) (hw : WeakDbar h f) :
    asL2 h-project (asL2 h)=asL2 (canonicalField f) := by
  have hF := hf.field_memLp
  have ha := weak_holomorphic_mem_analytic (hh.sub hF) (weak_dbar_difference hf df hh hw)
  have hmem : (hh.sub hF).toLp (h-canonicalField f) ∈ analyticSubspace :=
    (Submodule.span ℂ analyticVectors).le_topologicalClosure (Submodule.subset_span ha)
  have hz := hf.projection_zero
  have hp : project ((hh.sub hF).toLp (h-canonicalField f))=(hh.sub hF).toLp _ :=
    Submodule.starProjection_eq_self_iff.mpr hmem
  simp only [asL2,dif_pos hF] at hz
  rw [MemLp.toLp_sub hh hF,map_sub,hz,sub_zero] at hp
  simp only [asL2,dif_pos hh,dif_pos hF]
  rw [hp]; abel

/-- Appendix B.1 including every weak square-integrable primitive. -/
theorem SupercriticalSource.field_and_weak_projection {f : ℂ → ℂ} {t : ℝ} (hf : SupercriticalSource f t)
    (df : DifferentiableOn ℝ f upper) :
    ContinuousOn (canonicalField f) {z : ℂ | 0≤z.im} ∧
    (∃ C≥0, ∀ z : ℂ, 0≤z.im → ‖canonicalField f z‖≤C/(1+‖z‖)^(1+t)) ∧
    MemLp (canonicalField f) 2 upperArea ∧
    ∀ h : ℂ → ℂ, MemLp h 2 upperArea → WeakDbar h f → asL2 h-project (asL2 h)=asL2 (canonicalField f) :=
  ⟨(canonicalField_continuous hf.green.quadratic).continuousOn,hf.field_decay,hf.field_memLp,
    fun _ hh hw => hf.weak_residual_eq_field df hh hw⟩

end Liu
