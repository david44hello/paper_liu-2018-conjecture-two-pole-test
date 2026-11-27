module

public import Liu.EdgeRealBounds

@[expose] public section

noncomputable section
open Set Real MeasureTheory
namespace Liu

@[fun_prop] private theorem measurable_mk_complex {α : Type*} [MeasurableSpace α] {g h : α → ℝ}
    (hg : Measurable g) (hh : Measurable h) : Measurable (fun x => (⟨g x,h x⟩:ℂ)) :=
  Complex.measurableEquivRealProd.symm.measurable.comp (hg.prodMk hh)

theorem measurable_depthPoissonReal {f : ℂ → ℝ} (hf : Measurable f) (u : ℝ) :
    Measurable (fun x => depthPoissonReal u x f) := by
  have hm : Measurable (fun p : (ℝ×ℝ)×ℝ => poissonLine p.1.1 (p.1.2-u) p.2 * f ⟨p.2,p.1.2⟩) := by
    unfold poissonLine; fun_prop
  exact measurable_const.mul ((hm.stronglyMeasurable.integral_prod_right').integral_prod_right'
    (ν:=(volume:Measure ℝ).restrict (Ioi u))).measurable

theorem measurable_crossSource (a : ℝ) (q : ℂ) : Measurable (crossSource a q) := by
  have hd := measurable_deriv (edgeSum a q)
  unfold crossSource edgeSum at *
  fun_prop

private theorem poisson_enorm_mass (X : ℝ) {y : ℝ} (hy : 0<y) :
    ∫⁻ x, ‖poissonLine x y X‖ₑ = ‖π‖ₑ := by
  have he (x : ℝ) : poissonLine x y X = poissonLine X y x := by unfold poissonLine; ring
  simp_rw [he]
  have hi : Integrable (poissonLine X y) :=
    Integrable.of_integral_ne_zero ((poissonLine_integral X hy) ▸ pi_ne_zero)
  rw [←ofReal_integral_norm_eq_lintegral_enorm hi]
  have hp (x : ℝ) : ‖poissonLine X y x‖ = poissonLine X y x := Real.norm_of_nonneg (by unfold poissonLine; positivity)
  simp_rw [hp,poissonLine_integral X hy,Real.enorm_eq_ofReal pi_pos.le]

private theorem poisson_slice_lintegral {f : ℝ → ℝ} (hf : Measurable f) {y : ℝ} (hy : 0<y) :
    ∫⁻ x, ∫⁻ X, ‖poissonLine x y X*f X‖ₑ = ‖π‖ₑ * ∫⁻ X, ‖f X‖ₑ := by
  rw [lintegral_lintegral_swap (by
    apply Measurable.aemeasurable; unfold Function.uncurry poissonLine; fun_prop)]
  simp_rw [enorm_mul,lintegral_mul_const' ‖f _‖ₑ _ (enorm_ne_top (x:=f _)),poisson_enorm_mass _ hy]
  exact lintegral_const_mul' _ _ (enorm_ne_top (x:=π))

/-- Positive majorant obtained by integrating the absolute value before
performing either of the two Poisson integrations. -/
def poissonMagnitude (u x : ℝ) (f : ℂ → ℝ) : ENNReal :=
  ‖(1:ℝ)/π‖ₑ * ∫⁻ Y in Ioi u, ∫⁻ X, ‖poissonLine x (Y-u) X*f ⟨X,Y⟩‖ₑ

theorem depthPoissonReal_enorm_le (u x : ℝ) (f : ℂ → ℝ) :
    ‖depthPoissonReal u x f‖ₑ ≤ poissonMagnitude u x f := by
  unfold depthPoissonReal poissonMagnitude
  rw [enorm_mul]
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply (enorm_integral_le_lintegral_enorm _).trans
  exact lintegral_mono (fun Y => enorm_integral_le_lintegral_enorm _)

theorem poissonMagnitude_lintegral {f : ℂ → ℝ} (hf : Measurable f) {u : ℝ} (hu : 0≤u) :
    ENNReal.ofReal (1/π) * (∫⁻ x, poissonMagnitude u x f) ≤ ∫⁻ z, ‖f z‖ₑ ∂upperArea := by
  let μ := (volume:Measure ℝ).restrict (Ioi u)
  let K := fun (x Y X : ℝ) => poissonLine x (Y-u) X * f ⟨X,Y⟩
  have hm : Measurable (fun p : (ℝ×ℝ)×ℝ => ‖K p.1.1 p.1.2 p.2‖ₑ) := by dsimp [K,poissonLine]; fun_prop
  have h₂ : (∫⁻ x, poissonMagnitude u x f) = ∫⁻ Y, ∫⁻ X, ‖f ⟨X,Y⟩‖ₑ ∂volume ∂μ := by
    change (∫⁻ x, ‖(1:ℝ)/π‖ₑ*(∫⁻ Y, ∫⁻ X, ‖K x Y X‖ₑ ∂volume ∂μ)) = _
    rw [lintegral_const_mul' _ _ (enorm_ne_top (x:=(1:ℝ)/π)),lintegral_lintegral_swap (hm.lintegral_prod_right'.aemeasurable)]
    have he : (∫⁻ Y, ∫⁻ x, ∫⁻ X, ‖K x Y X‖ₑ ∂volume ∂volume ∂μ) =
        ∫⁻ Y, ‖π‖ₑ*(∫⁻ X, ‖f ⟨X,Y⟩‖ₑ) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=u))] with Y hY
      exact poisson_slice_lintegral (f:=fun X => f ⟨X,Y⟩) (by fun_prop) (sub_pos.mpr hY)
    rw [he,lintegral_const_mul' _ _ (enorm_ne_top (x:=π)),←mul_assoc,←enorm_mul,one_div_mul_cancel pi_ne_zero,enorm_one,one_mul]
  have h₃ : (∫⁻ Y, ∫⁻ X, ‖f ⟨X,Y⟩‖ₑ ∂volume ∂μ) ≤ ∫⁻ Y in Ioi (0:ℝ), ∫⁻ X, ‖f ⟨X,Y⟩‖ₑ :=
    lintegral_mono_set (Ioi_subset_Ioi hu)
  have hslice : (∫⁻ z in upper, ‖f z‖ₑ) = ∫⁻ Y in Ioi (0:ℝ), ∫⁻ X, ‖f ⟨X,Y⟩‖ₑ := by
    let e := Complex.measurableEquivRealProd.symm
    let F := upper.indicator (fun z => ‖f z‖ₑ)
    have hp := Complex.volume_preserving_equiv_real_prod.symm.lintegral_comp_emb e.measurableEmbedding F
    rw [←lintegral_indicator upper_open.measurableSet,←hp,Measure.volume_eq_prod,
      lintegral_prod_symm _ (show Measurable (fun p : ℝ×ℝ => F (e p)) by
        exact (hf.enorm.indicator upper_open.measurableSet).comp e.measurable).aemeasurable,
      ←lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro Y
    by_cases hY : 0<Y
    · rw [indicator_of_mem (show Y∈Ioi (0:ℝ) from hY)]
      exact lintegral_congr (fun X => indicator_of_mem (show e (X,Y)∈upper from hY) _)
    · rw [indicator_of_notMem (show Y∉Ioi (0:ℝ) from hY)]
      have he (X : ℝ) : F (e (X,Y))=0 := indicator_of_notMem (show e (X,Y)∉upper from hY) _
      simp only [he,lintegral_zero]
  unfold upperArea area
  rw [Measure.restrict_smul,lintegral_smul_measure,smul_eq_mul,hslice]
  exact mul_le_mul_of_nonneg_left (h₂.le.trans h₃) zero_le

theorem depthPoissonReal_lintegral {f : ℂ → ℝ} (hf : Measurable f) {u : ℝ} (hu : 0≤u) :
    ENNReal.ofReal (1/π) * (∫⁻ x, ‖depthPoissonReal u x f‖ₑ) ≤ ∫⁻ z, ‖f z‖ₑ ∂upperArea :=
  (mul_le_mul_of_nonneg_left (lintegral_mono (fun x => depthPoissonReal_enorm_le u x f)) zero_le).trans
    (poissonMagnitude_lintegral hf hu)

end Liu
