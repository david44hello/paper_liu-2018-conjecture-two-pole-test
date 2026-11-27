module

public import Liu.BoundaryField
public import Liu.PoissonLine

@[expose] public section

noncomputable section
open MeasureTheory Real Set
open scoped ComplexConjugate
namespace Liu

def traceDensity (S : ℂ → ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  ((2*w.im/‖w-(x:ℂ)‖^2:ℝ):ℂ)*source S w

theorem PickSum.traceDensity_integrable {n : ℕ} (p : PickSum n) (x : ℝ) :
    Integrable (traceDensity p.value x) upperArea := by
  classical
  have hL : 0 ≤ p.derivativeBound/2 := by
    simpa using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  have hi := boundaryTrace_integrable hL p.source_measurable p.source_continuousOn
    (fun _ hz => p.source_decay hz) x
  have h := measurePreserving_add_left (volume:Measure ℂ) (x:ℂ)
  have h' : MeasurePreserving (fun v : ℂ => (x:ℂ)+v) area area :=
    ⟨h.measurable,by unfold area; rw [Measure.map_smul _ h.measurable.aemeasurable,h.map_eq]⟩
  apply (integrable_indicator_iff upper_open.measurableSet).mp
  apply (h'.integrable_comp_emb (Homeomorph.addLeft (x:ℂ)).measurableEmbedding).mp
  apply hi.congr
  filter_upwards with v
  by_cases hv : 0 < v.im
  · have hu : (x:ℂ)+v ∈ upper := by simpa [upper] using hv
    simp [boundaryTraceIntegrand,Function.comp_apply,traceDensity,hv,hu]
  · have hu : (x:ℂ)+v ∉ upper := by simpa [upper] using hv
    simp [boundaryTraceIntegrand,Function.comp_apply,hv,hu]

theorem upperArea_slices {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E)
    (hf : Integrable f upperArea) :
    ∫ w, f w ∂upperArea = (1/π:ℝ) • ∫ y in Ioi (0:ℝ), ∫ X : ℝ, f ⟨X,y⟩ := by
  classical
  let F := upper.indicator f
  have hV : Integrable F volume := by
    apply (integrable_indicator_iff upper_open.measurableSet).mpr
    unfold upperArea area at hf
    rw [Measure.restrict_smul] at hf
    exact (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
      ENNReal.ofReal_ne_top).mp hf
  let e := Complex.measurableEquivRealProd.symm
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have hF := (hp.integrable_comp_emb e.measurableEmbedding).mpr hV
  have h := hp.integral_comp e.measurableEmbedding F
  unfold upperArea area
  rw [Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),
    ←integral_indicator upper_open.measurableSet]
  change (1/π:ℝ) • (∫ w, F w) = _
  rw [←h]
  congr 1
  rw [←integral_indicator measurableSet_Ioi]
  rw [Measure.volume_eq_prod] at hF ⊢
  change (∫ v, (F ∘ e) v ∂(volume:Measure ℝ).prod volume) = _
  rw [integral_prod_symm _ hF]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : 0<y
  · rw [indicator_of_mem (show y ∈ Ioi (0:ℝ) from hy)]
    apply integral_congr_ae
    filter_upwards with X
    change upper.indicator f ⟨X,y⟩ = f ⟨X,y⟩
    exact indicator_of_mem (show (⟨X,y⟩:ℂ) ∈ upper from hy) f
  · rw [indicator_of_notMem (show y ∉ Ioi (0:ℝ) from hy)]
    have he (X : ℝ) : F (e (X,y)) = 0 := indicator_of_notMem (show (⟨X,y⟩:ℂ) ∉ upper from hy) f
    change (∫ X : ℝ, F (e (X,y))) = 0
    simp only [he,integral_zero]

def singlePick (m a b : ℝ) (hm : 0 < m) (hb : 0 < b) : PickSum 1 where
  nonempty := by decide
  weight := fun _ => m
  location := fun _ => (a:ℂ)-(b:ℂ)*Complex.I
  pos := fun _ => hm
  below := fun _ => by simp [hb]

theorem singlePick_value (m a b : ℝ) (hm : 0 < m) (hb : 0 < b) :
    (singlePick m a b hm hb).value = pole m ((a:ℂ)-(b:ℂ)*Complex.I) := by
  funext z
  simp [singlePick,PickSum.value]

theorem singlePole_source {m : ℝ} {w z : ℂ} (hm : 0 < m) (hz : z≠w) :
    source (pole m w) z = (Complex.I/2)*((m/‖z-w‖^2:ℝ):ℂ) := by
  simp only [source,(pole_hasDerivAt hz).deriv,pole,map_div₀,map_neg,map_pow,
    Complex.conj_ofReal,Complex.ofReal_div,Complex.ofReal_pow]
  rw [←Complex.mul_conj' (z-w)]
  have h := sub_ne_zero.mpr hz
  have hc : conj (z-w) ≠ 0 := by
    intro he
    exact h (by simpa only [Complex.conj_conj,map_zero] using congrArg (fun u : ℂ => conj u) he)
  have hmc := Complex.ofReal_ne_zero.mpr hm.ne'
  field_simp [h,hc,hmc] <;> ring

end Liu
