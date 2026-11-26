import Liu.DepthFieldComparison
import Liu.ShiftCutoff

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped Topology ComplexConjugate
namespace Liu

def physicalDensity (S : ℂ → ℂ) (z : ℂ) := k₀*‖S z‖^2-‖field S z‖^2
def depthBand (h : ℝ) := Complex.im ⁻¹' Ioc 0 h

private theorem depthBand_measurable (h : ℝ) : MeasurableSet (depthBand h) :=
  measurableSet_Ioc.preimage Complex.measurable_im

theorem PickSum.density_band_integrable {n : ℕ} (p : PickSum n) (h : ℝ) :
    IntegrableOn (physicalDensity p.value) (depthBand h) area := by
  obtain ⟨A,hA,H⟩ := p.field_decay
  let B := k₀*p.bound^2+A^2
  have hk : 0≤k₀ := by unfold k₀; positivity
  have hb := p.bound_pos
  let f := fun x : ℝ => B*(1+‖x‖)^(-(2:ℝ))
  let g := (Ioc (0:ℝ) h).indicator (fun _ => (1:ℝ))
  have hf : Integrable f volume := (integrable_one_add_norm (by norm_num)).const_mul _
  have hg : Integrable g volume := (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have hprod := hf.mul_prod hg
  have hp := Complex.volume_preserving_equiv_real_prod
  have hG : Integrable (fun w : ℂ => f w.re*g w.im) volume := by
    simpa only [Function.comp_def,Complex.measurableEquivRealProd_apply,Measure.volume_eq_prod] using
      (hp.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding).mpr hprod
  have hval : Measurable p.value := by unfold PickSum.value pole; fun_prop
  have hD : Measurable (physicalDensity p.value) := by
    have hfield := field_measurable p.value
    unfold physicalDensity; fun_prop
  apply (integrable_indicator_iff (depthBand_measurable h)).mp
  apply (hG.smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).mono' (hD.indicator (depthBand_measurable h)).aestronglyMeasurable
  apply ae_of_all; intro w
  by_cases hw : w∈depthBand h
  · have hu : w∈upper := hw.1
    have hr : 1+‖w.re‖ ≤ 1+‖w‖ := add_le_add (le_refl _) (Complex.abs_re_le_norm _)
    have hs := (p.global_decay (le_of_lt hu)).trans (div_le_div_of_nonneg_left hb.le (by positivity) hr)
    have hv := (H w hu).trans (div_le_div_of_nonneg_left hA (by positivity) hr)
    rw [indicator_of_mem hw,show g w.im=1 from indicator_of_mem (show w.im∈Ioc 0 h from hw) _,mul_one]
    apply (norm_sub_le ..).trans
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hk (sq_nonneg _)),abs_of_nonneg (sq_nonneg _)]
    apply (add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs 2) hk)
      (pow_le_pow_left₀ (norm_nonneg _) hv 2)).trans_eq
    dsimp only [f,B]; rw [rpow_neg (by positivity),rpow_two,div_pow,div_pow]; ring
  · rw [indicator_of_notMem hw,norm_zero,show g w.im=0 from indicator_of_notMem (show w.im∉Ioc 0 h from hw) _,mul_zero]

/-- Translation of the old optimal witness deletes exactly the strip. The
difference between the two circular cutoffs vanishes in the radial limit. -/
theorem PickSum.depth_deficit_difference {n : ℕ} (p : PickSum n) {h : ℝ} (hh : 0≤h) :
    let q := p.deeper h hh
    let W := depthTranslate (optimalWitness p.value) h
    deficit q.value-deficit p.value =
      -(∫ z in depthBand h, physicalDensity p.value z ∂area)+energy (witnessDifference q.value W) := by
  let q := p.deeper h hh
  let W := depthTranslate (optimalWitness p.value) h
  let D := physicalDensity p.value
  let c := (h:ℂ)*Complex.I
  let T := fun R : ℝ => upper ∩ ball c R
  let A := fun R : ℝ => depthBand h ∩ ball c R
  let U := fun R : ℝ => {w : ℂ | h<w.im} ∩ ball c R
  have hcl : ∀ R : ℝ, U R=T R \ A R := by
    intro R; ext w
    change (h<w.im ∧ w∈ball c R) ↔ (0<w.im ∧ w∈ball c R) ∧ ¬((0<w.im ∧ w.im≤h) ∧ w∈ball c R)
    constructor
    · rintro ⟨hw,hb⟩; exact ⟨⟨hh.trans_lt hw,hb⟩,fun k => (not_le.mpr hw) k.1.2⟩
    · rintro ⟨⟨hw,hb⟩,he⟩
      exact ⟨lt_of_not_ge fun H => he ⟨⟨hw,H⟩,hb⟩,hb⟩
  have hmA (R : ℝ) : MeasurableSet (A R) := (depthBand_measurable h).inter isOpen_ball.measurableSet
  have hmU (R : ℝ) : MeasurableSet (U R) := (measurableSet_lt measurable_const Complex.measurable_im).inter isOpen_ball.measurableSet
  have huA : (⋃ R : ℝ, A R)=depthBand h := by
    ext w; constructor
    · rintro ⟨_,⟨R,rfl⟩,hw⟩; exact hw.1
    · intro hw; exact mem_iUnion.mpr ⟨dist w c+1,hw,by simp [mem_ball]⟩
  have hiA := p.density_band_integrable h
  have hlimA : Tendsto (fun R => ∫ z in A R,D z ∂area) atTop (𝓝 (∫ z in depthBand h,D z ∂area)) := by
    rw [←huA] at hiA ⊢
    exact tendsto_setIntegral_of_monotone hmA
      (show Monotone A from fun _ _ h => inter_subset_inter_right _ (ball_subset_ball h)) hiA
  have hlimT := offset_deficit_limit p.bound_pos.le (fun z hz => p.global_decay (le_of_lt hz)) p.finite_part.1 c
  have hp : MeasurePreserving (fun z : ℂ => z+c) area area := by
    have e := measurePreserving_add_right (volume:Measure ℂ) c
    exact ⟨e.measurable,by unfold area; rw [Measure.map_smul _ e.measurable.aemeasurable,e.map_eq]⟩
  have hew (R : ℝ) : truncatedWitness q.value W R = ∫ z in U R,D z ∂area := by
    have he := hp.setIntegral_preimage_emb (Homeomorph.addRight c).measurableEmbedding D (U R)
    have hpre : (fun z : ℂ => z+c) ⁻¹' U R=halfDisc R := by
      ext z; change (h<(z+c).im ∧ z+c∈ball c R) ↔ 0<z.im ∧ z∈ball 0 R
      simp [c,mem_ball,dist_eq_norm]
    rw [hpre] at he
    apply Eq.trans _ he
    apply setIntegral_congr_fun (upper_open.measurableSet.inter isOpen_ball.measurableSet)
    intro z hz
    have hy : 0≤(z+c).im := by dsimp [c]; simp; linarith [show 0<z.im from hz.1]
    have hn : p.value (z+c)≠0 := by intro e; have H := p.value_im_pos hy; simp [e] at H
    have hs : q.value z=p.value (z+c) := congrFun (p.deeper_value hh) z
    change k₀*‖q.value z‖^2-‖q.value z‖^2*‖((q.value z).arg:ℂ)-W z‖^2=_
    dsimp only [D,physicalDensity]
    rw [hs,←mul_pow,←norm_mul,field_eq_witness_product hn]; rfl
  have hdiff : ∀ᶠ R : ℝ in atTop, truncatedWitness q.value W R=(∫ z in T R,D z ∂area)-(∫ z in A R,D z ∂area) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    have hi : IntegrableOn D (T R) area := (p.deficit_local_integrable (R+‖c‖)).mono_set (by
      intro z hz
      have H := norm_add_le (z-c) c
      rw [sub_add_cancel] at H
      exact ⟨hz.1,by simpa using H.trans_lt (add_lt_add_left (show ‖z-c‖<R by simpa only [mem_ball,dist_eq_norm] using hz.2) _)⟩)
    rw [hew,hcl,setIntegral_sdiff (hmA _) hi (fun _ hw => ⟨hw.1.1,hw.2⟩)]
  have hw := q.witness_identity.2 W (isWitness_depthTranslate p.optimalWitness_isWitness hh)
  have hl : Tendsto (truncatedWitness q.value W) atTop (𝓝 (deficit p.value-∫ z in depthBand h,D z ∂area)) :=
    (hlimT.sub hlimA).congr' (hdiff.mono fun R hh => hh.symm)
  have HH := tendsto_nhds_unique hw.2.1 hl
  change deficit q.value-deficit p.value= -(∫ z in depthBand h,D z ∂area)+energy (witnessDifference q.value W)
  linarith only [HH]

end Liu
