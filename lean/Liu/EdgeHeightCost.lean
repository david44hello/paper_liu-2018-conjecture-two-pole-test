import Liu.EdgeWeightedTrace
import Liu.PoleArea

noncomputable section
open Set Real MeasureTheory
namespace Liu

/-- Reciprocal of the height weight for Cauchy–Schwarz. -/
def edgeHeightCost (y : ℝ) : ℝ := if y≤0 then 1 else if y≤4 then sqrt y else y^2

theorem edgeHeightCost_pos (y : ℝ) : 0<edgeHeightCost y := by
  unfold edgeHeightCost
  split_ifs with h h'
  · norm_num
  · exact sqrt_pos.mpr (lt_of_not_ge h)
  · exact sq_pos_of_pos (lt_of_not_ge h)

theorem edgeHeightCost_measurable : Measurable edgeHeightCost := by
  unfold edgeHeightCost
  apply Measurable.ite measurableSet_Iic measurable_const
  exact Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)

private theorem heightWeight_mass {u : ℝ} (hu : 0≤u) :
    (∫⁻ Y in Ioi u, ‖((sqrt (edgeHeightCost Y))⁻¹)^2‖ₑ)≤ENNReal.ofReal 5 := by
  let L := (Ioc (0:ℝ) 4).indicator (fun y => y^(-(1/2:ℝ)))
  let T := (Ioi (4:ℝ)).indicator (fun y => y^(-(2:ℝ)))
  have hTi : Integrable T := (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num))
  have hL : (∫ Y, L Y)=4 := by
    rw [show L=(Ioc (0:ℝ) 4).indicator (fun y => y^(-(1/2:ℝ))) from rfl,integral_indicator measurableSet_Ioc,
      ←intervalIntegral.integral_of_le (by norm_num),integral_rpow (Or.inl (by norm_num))]
    norm_num [←sqrt_eq_rpow]
  have hLi : Integrable L := Integrable.of_integral_ne_zero (hL ▸ (by norm_num))
  have hT : (∫ Y, T Y)=1/4 := by
    dsimp only [T]; rw [integral_indicator measurableSet_Ioi,integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
    norm_num [rpow_neg_one]
  have he (Y : ℝ) (hy : 0<Y) : ((sqrt (edgeHeightCost Y))⁻¹)^2 = L Y+T Y := by
    rw [inv_pow,sq_sqrt (edgeHeightCost_pos Y).le]
    by_cases h : Y≤4
    · simp [L,T,edgeHeightCost,hy.not_ge,hy,h,sqrt_eq_rpow,rpow_neg hy.le]
    · simp [L,T,edgeHeightCost,hy.not_ge,hy,h,lt_of_not_ge h,rpow_neg hy.le]
  have hn (Y : ℝ) : 0≤L Y+T Y := add_nonneg
    (indicator_nonneg (fun y hy => rpow_nonneg (le_of_lt hy.1) _) _)
    (indicator_nonneg (fun y (hy : y∈Ioi (4:ℝ)) => rpow_nonneg (le_trans (by norm_num) hy.le) _) _)
  apply le_trans _ (show (∫⁻ Y, ENNReal.ofReal (L Y+T Y))≤ENNReal.ofReal 5 by
    rw [←ofReal_integral_eq_lintegral_ofReal (f:=fun Y => L Y+T Y) (hLi.add hTi) (ae_of_all _ hn),integral_add hLi hTi,hL,hT]
    exact ENNReal.ofReal_le_ofReal (by norm_num))
  apply le_trans _ (setLIntegral_le_lintegral (Ioi u) (fun Y => ENNReal.ofReal (L Y+T Y)))
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=u))] with Y hY
  rw [he Y (hu.trans_lt hY),Real.enorm_eq_ofReal (hn Y)]

/-- Convert an area bound for the weighted squared source into a normalized
squared boundary norm and L² membership, even at u=0. -/
theorem depthPoissonReal_sq_of_area {f : ℂ → ℝ} (hf : Measurable f) {u : ℝ} (hu : 0≤u)
    (harea : Integrable (fun z => f z^2*edgeHeightCost z.im) upperArea) :
    let q := fun x => depthPoissonReal u x f
    MemLp q 2 volume ∧ (∫ x, q x^2)/π≤5*∫ z, f z^2*edgeHeightCost z.im ∂upperArea := by
  let w := fun y => (sqrt (edgeHeightCost y))⁻¹
  let g := fun z : ℂ => f z*sqrt (edgeHeightCost z.im)
  have hw : Measurable w := edgeHeightCost_measurable.sqrt.inv
  have hg : Measurable g := hf.mul (edgeHeightCost_measurable.comp Complex.measurable_im).sqrt
  have he : (fun z : ℂ => w z.im*g z)=f := by
    funext z; dsimp only [w,g]; field_simp [(sqrt_pos.mpr (edgeHeightCost_pos z.im)).ne']
  have hg₂ (z : ℂ) : g z^2=f z^2*edgeHeightCost z.im := by dsimp [g]; rw [mul_pow,sq_sqrt (edgeHeightCost_pos _).le]
  have h := depthPoissonReal_weighted_L2 hu hw hg (by norm_num : (0:ℝ)≤5) (heightWeight_mass hu)
  rw [he] at h
  simp_rw [hg₂,Real.enorm_eq_ofReal (mul_nonneg (sq_nonneg _) (edgeHeightCost_pos _).le)] at h
  rw [←ofReal_integral_eq_lintegral_ofReal harea (ae_of_all _ (fun z => mul_nonneg (sq_nonneg _) (edgeHeightCost_pos _).le)),
    ←ENNReal.ofReal_mul (by norm_num)] at h
  let q := fun x => depthPoissonReal u x f
  have hqm : Measurable q := measurable_depthPoissonReal hf u
  have hs : Integrable (fun x => q x^2) := by
    refine ⟨(hqm.pow_const 2).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_enorm,lt_top_iff_ne_top]
    simp_rw [enorm_pow]
    intro e
    change (∫⁻ x, ‖q x‖ₑ^2)=⊤ at e
    change ENNReal.ofReal (1/π)*(∫⁻ x, ‖q x‖ₑ^2)≤_ at h
    rw [e,ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h)
  have hmass : (∫⁻ x, ‖q x‖ₑ^2)=ENNReal.ofReal (∫ x, q x^2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hs (ae_of_all _ (fun x => sq_nonneg (q x)))]
    apply lintegral_congr; intro x; rw [←enorm_pow,Real.enorm_eq_ofReal (sq_nonneg _)]
  change ENNReal.ofReal (1/π)*(∫⁻ x, ‖q x‖ₑ^2)≤_ at h
  rw [hmass,←ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_le_ofReal_iff (by
    apply mul_nonneg (by norm_num) (integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (edgeHeightCost_pos _).le)))] at h
  refine ⟨(memLp_two_iff_integrable_sq hqm.aestronglyMeasurable).mpr hs,?_⟩
  simpa only [q,div_eq_mul_inv,one_mul,mul_comm π⁻¹] using h

end Liu
