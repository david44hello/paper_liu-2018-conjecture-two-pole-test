import Liu.Reflection
import Liu.Denominator
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section
open Set MeasureTheory Filter Metric Real
open scoped Topology
namespace Liu

private def shiftedDisc (x R : ℝ) : Set ℂ := upper ∩ ball (x:ℂ) R

private theorem shiftedDisc_measurable (x R : ℝ) : MeasurableSet (shiftedDisc x R) :=
  upper_open.measurableSet.inter Metric.isOpen_ball.measurableSet

private theorem halfDisc_measurable (R : ℝ) : MeasurableSet (halfDisc R) :=
  upper_open.measurableSet.inter Metric.isOpen_ball.measurableSet

private theorem offsetDisc_sandwich (x : ℂ) (R : ℝ) :
    halfDisc (R-‖x‖) ⊆ (upper ∩ ball x R) ∧ (upper ∩ ball x R) ⊆ halfDisc (R+‖x‖) := by
  constructor
  · intro z hz
    refine ⟨hz.1,?_⟩
    have hi : ‖z‖ < R-‖x‖ := by simpa using hz.2
    rw [mem_ball,dist_eq_norm]
    exact (norm_sub_le ..).trans_lt (by linarith)
  · intro z hz
    refine ⟨hz.1,?_⟩
    have hi : ‖z-x‖ < R := by simpa only [mem_ball,dist_eq_norm] using hz.2
    have h := norm_add_le (z-x) x
    rw [sub_add_cancel] at h
    simpa using (show ‖z‖ < R+‖x‖ by linarith)

private theorem shiftedDisc_sandwich (x R : ℝ) :
    halfDisc (R-|x|) ⊆ shiftedDisc x R ∧ shiftedDisc x R ⊆ halfDisc (R+|x|) := by
  simpa only [shiftedDisc,Complex.norm_real,Real.norm_eq_abs] using offsetDisc_sandwich (x:ℂ) R

private theorem area_real_ball (r : ℝ) (hr : 0≤r) : area.real (ball (0:ℂ) r) = r^2 := by
  simp [Measure.real,area,Complex.volume_ball,ENNReal.toReal_ofReal hr,NNReal.coe_real_pi]
  rw [ENNReal.toReal_ofReal (by positivity : 0≤π⁻¹)]
  field_simp

private def density (S : ℂ → ℂ) (z : ℂ) : ℝ := k₀*‖S z‖^2-‖field S z‖^2

/-- A fixed-width annular piece costs at most O(1/R) in the positive direction.
The negative field term can only decrease its signed integral. -/
private theorem annular_increment {S : ℂ → ℂ} {B T R : ℝ} (hB : 0≤B) (hT : 0≤T)
    (hs : ∀ z ∈ upper, ‖S z‖ ≤ B/(1+‖z‖)) (hR : 2*T+1≤R)
    {s t : Set ℂ} (hlo : halfDisc (R-T) ⊆ s) (hst : s ⊆ t) (hhi : t ⊆ halfDisc (R+T))
    (hsM : MeasurableSet s) (htM : MeasurableSet t)
    (hint : IntegrableOn (density S) (halfDisc (R+T)) area) :
    (∫ z in t, density S z ∂area) - (∫ z in s, density S z ∂area) ≤ 16*k₀*B^2*T/R := by
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  have hr : 0<R := by linarith
  have hk : 0≤k₀ := by unfold k₀; positivity
  let outer := ball (0:ℂ) (R+T)
  let inner := ball (0:ℂ) (R-T)
  have hfin : area outer ≠ ⊤ := (measure_ball_lt_top ..).ne
  have hsub : t \ s ⊆ outer \ inner := by
    intro z hz
    obtain ⟨hu,ho⟩ := hhi hz.1
    exact ⟨ho,fun hi => hz.2 (hlo ⟨hu,hi⟩)⟩
  have he : area.real (t \ s) ≤ 4*R*T := by
    apply (measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset hfin)).trans
    rw [measureReal_sdiff (ball_subset_ball (by linarith : R-T≤R+T)) Metric.isOpen_ball.measurableSet hfin,
      area_real_ball _ (by linarith),area_real_ball _ (by linarith)]
    linarith only [show (R+T)^2-(R-T)^2 = 4*R*T by ring]
  let K := k₀*(2*B/R)^2
  have hK : 0≤K := mul_nonneg hk (sq_nonneg _)
  have hf : area (t \ s) ≠ ⊤ := measure_ne_top_of_subset (hsub.trans sdiff_subset) hfin
  rw [←setIntegral_sdiff hsM (hint.mono_set hhi) hst]
  calc
    _ ≤ ∫ _ in t \ s, K ∂area := by
      apply setIntegral_mono_on (hint.mono_set (sdiff_subset.trans hhi)) (integrableOn_const hf) (htM.diff hsM)
      intro z hz
      have hu := (hhi hz.1).1
      have hn : R-T ≤ ‖z‖ := by simpa [inner] using (hsub hz).2
      have hb : ‖S z‖ ≤ 2*B/R := (hs z hu).trans (by
        apply (div_le_div_iff₀ (by positivity) hr).mpr
        nlinarith [mul_le_mul_of_nonneg_left (show R ≤ 2*(1+‖z‖) by linarith) hB])
      exact (sub_le_self _ (sq_nonneg _)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hb 2) hk)
    _ = area.real (t \ s)*K := by rw [setIntegral_const,smul_eq_mul]
    _ ≤ (4*R*T)*K := mul_le_mul_of_nonneg_right he hK
    _ = _ := by dsimp [K]; field_simp [hr.ne'] <;> ring

private theorem horizontal_area (x : ℝ) : MeasurePreserving (fun z : ℂ => z+(x:ℂ)) area area := by
  have h := measurePreserving_add_right (volume:Measure ℂ) (x:ℂ)
  exact ⟨h.measurable,by unfold area; rw [Measure.map_smul _ h.measurable.aemeasurable,h.map_eq]⟩

private theorem preimage_shiftedDisc (x R : ℝ) :
    (fun z : ℂ => z+(x:ℂ)) ⁻¹' shiftedDisc x R = halfDisc R := by
  ext z
  simp [shiftedDisc,halfDisc,upper,mem_ball,dist_eq_norm]

/-- A fixed offset of the centre of the circular cutoff preserves the signed
finite part on the original upper half-plane. -/
theorem offset_deficit_limit {S : ℂ → ℂ} {B : ℝ} (hB : 0≤B)
    (hs : ∀ z∈upper, ‖S z‖≤B/(1+‖z‖)) (hf : finitePartExists S) (c : ℂ) :
    Tendsto (fun R : ℝ => ∫ z in upper ∩ ball c R, k₀*‖S z‖^2-‖field S z‖^2 ∂area)
      atTop (𝓝 (deficit S)) := by
  change Tendsto (fun R : ℝ => ∫ z in upper ∩ ball c R, density S z ∂area) atTop (𝓝 (deficit S))
  let T := ‖c‖
  have hT : 0≤T := norm_nonneg _
  have h₁ : Tendsto (fun R => truncatedDeficit S (R+T)) atTop (𝓝 (deficit S)) :=
    (finite_part_limit hf).comp (tendsto_atTop_add_const_right _ T tendsto_id)
  have h₂ : Tendsto (fun R => truncatedDeficit S (R-T)) atTop (𝓝 (deficit S)) := by
    simpa [sub_eq_add_neg,Function.comp_def] using (finite_part_limit hf).comp (tendsto_atTop_add_const_right _ (-T) tendsto_id)
  let E := fun R => 16*k₀*B^2*T/R
  have hE : Tendsto E atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa only [sub_zero] using h₁.sub hE)
    (by simpa only [add_zero] using h₂.add hE)
  · filter_upwards [eventually_ge_atTop (2*T+1)] with R hR
    obtain ⟨hl,hu⟩ := offsetDisc_sandwich c R
    have h := annular_increment hB hT hs hR hl hu Subset.rfl (upper_open.measurableSet.inter isOpen_ball.measurableSet)
      (halfDisc_measurable _) (hf.1 _ (by linarith))
    change (∫ z in halfDisc (R+T), density S z ∂area)-E R ≤ _
    dsimp [E]; linarith
  · filter_upwards [eventually_ge_atTop (2*T+1)] with R hR
    obtain ⟨hl,hu⟩ := offsetDisc_sandwich c R
    have h := annular_increment hB hT hs hR Subset.rfl hl hu (halfDisc_measurable _)
      (upper_open.measurableSet.inter isOpen_ball.measurableSet) (hf.1 _ (by linarith))
    change _ ≤ (∫ z in halfDisc (R-T), density S z ∂area)+E R
    dsimp [E]; linarith

theorem shifted_finite_part {S : ℂ → ℂ} {B : ℝ} (hB : 0≤B)
    (hs : ∀ z ∈ upper, ‖S z‖ ≤ B/(1+‖z‖)) (hf : finitePartExists S) (x : ℝ) :
    finitePartExists (fun z => S (z+(x:ℂ))) ∧
      deficit (fun z => S (z+(x:ℂ))) = deficit S := by
  let T := |x|
  have hT : 0≤T := abs_nonneg _
  let e := (Homeomorph.addRight (x:ℂ)).measurableEmbedding
  have he (z : ℂ) : density (fun w => S (w+(x:ℂ))) z = density S (z+(x:ℂ)) := by
    rw [density,field_shift]; rfl
  have changeDisc (R : ℝ) : truncatedDeficit (fun z => S (z+(x:ℂ))) R =
      ∫ z in shiftedDisc x R, density S z ∂area := by
    have h := (horizontal_area x).setIntegral_preimage_emb e (density S) (shiftedDisc x R)
    rw [preimage_shiftedDisc] at h
    exact (setIntegral_congr_fun (halfDisc_measurable R) (fun z _ => he z)).trans h
  have ht : Tendsto (truncatedDeficit (fun z => S (z+(x:ℂ)))) atTop (𝓝 (deficit S)) :=
    (offset_deficit_limit hB hs hf (x:ℂ)).congr fun R => (changeDisc R).symm
  refine ⟨⟨?_,⟨_,ht⟩⟩,ht.limUnder_eq⟩
  intro R hR
  have hi := ((horizontal_area x).integrableOn_comp_preimage e).mpr
    ((hf.1 (R+T) (by linarith)).mono_set (shiftedDisc_sandwich x R).2)
  rw [preimage_shiftedDisc] at hi
  simpa only [density,Function.comp_def,field_shift] using hi

theorem Pair.shift_deficit (p : Pair) (hf : finitePartExists p.value) (x : ℝ) :
    finitePartExists (p.shift x).value ∧ deficit (p.shift x).value = deficit p.value := by
  have he : (p.shift x).value = fun z => p.value (z+(x:ℂ)) := by
    funext z
    simp [Pair.shift,Pair.value,pole,sub_sub_eq_add_sub,add_comm,add_left_comm]
  rw [he]
  apply shifted_finite_part p.toPick.bound_pos.le _ hf
  intro z hz
  simpa [PickSum.value,Pair.toPick,Pair.value,Fin.sum_univ_two] using p.toPick.global_decay (le_of_lt hz)

theorem finitePart_invariances_of_existence (h : ∀ p : Pair, finitePartExists p.value) :
    FinitePartInvariances :=
  ⟨fun p x => (p.shift_deficit (h p) x).2,Pair.reflect_deficit,
    fun p d hd => p.dilate_deficit (h p) hd,fun p c hc => p.scaleMass_deficit (h p) c hc⟩

end Liu
