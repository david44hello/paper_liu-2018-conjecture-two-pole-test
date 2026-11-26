import Liu.Symmetry

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu

def dilateFunction (S : ℂ → ℂ) (d : ℝ) (z : ℂ) : ℂ := (d:ℂ)*S (d • z)

theorem source_dilate (S : ℂ → ℂ) {d : ℝ} (hd : 0<d) (z : ℂ) :
    source (dilateFunction S d) z = (d:ℂ)^2*source S (d • z) := by
  change source (fun w => (d:ℂ)*S ((d:ℂ)*w)) z = _
  rw [source_mass_scale]
  simp only [source,deriv_comp_mul_left,smul_eq_mul,map_mul,Complex.conj_ofReal,Complex.real_smul]
  ring

theorem area_integral_dilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) {d : ℝ} (hd : 0<d) {s t : Set ℂ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hpre : ∀ z : ℂ, z ∈ s ↔ d • z ∈ t) :
    ∫ z in s, f (d • z) ∂area = (d^2)⁻¹ • ∫ w in t, f w ∂area := by
  classical
  have h := Measure.integral_comp_smul_of_nonneg volume (t.indicator f) d (hR:=hd.le)
  have eqn (z : ℂ) : t.indicator f (d • z) = s.indicator (fun w => f (d • w)) z := by
    by_cases hz : z ∈ s
    · simp only [indicator_of_mem hz,indicator_of_mem ((hpre z).mp hz)]
    · simp only [indicator_of_notMem hz,indicator_of_notMem (mt (hpre z).mpr hz)]
  simp only [eqn,integral_indicator hs,integral_indicator ht,Complex.finrank_real_complex] at h
  unfold area
  simp only [Measure.restrict_smul,integral_smul_measure,h]
  exact smul_comm .. 

theorem greenLog_dilate {d : ℝ} (hd : 0<d) (z w : ℂ) :
    greenLog (d • z) (d • w) = greenLog z w := by
  simp only [greenLog,Complex.real_smul,map_mul,Complex.conj_ofReal,←mul_sub,norm_mul,
    mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (Complex.ofReal_ne_zero.mpr hd.ne'))]

theorem potential_dilate (S : ℂ → ℂ) {d : ℝ} (hd : 0<d) :
    potential (dilateFunction S d) = fun z => potential S (d • z) := by
  funext z
  let f := fun w : ℂ => (greenLog (d • z) w:ℂ)*source S w
  have pre (w : ℂ) : w ∈ upper ↔ d • w ∈ upper := by
    change 0<w.im ↔ 0<(d • w).im
    simp [Complex.real_smul,hd]
  have h := area_integral_dilate f hd upper_open.measurableSet upper_open.measurableSet pre
  change (∫ w in upper, (greenLog z w:ℂ)*source (dilateFunction S d) w ∂area) = ∫ w in upper, f w ∂area
  calc
    _ = ∫ w in upper, (d:ℂ)^2*f (d • w) ∂area := by
      apply integral_congr_ae
      filter_upwards with w
      simp only [f,greenLog_dilate hd,source_dilate S hd]
      ring
    _ = _ := by
      rw [integral_const_mul,h,Complex.real_smul]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hd.ne']

theorem field_dilate (S : ℂ → ℂ) {d : ℝ} (hd : 0<d) (z : ℂ) :
    field (dilateFunction S d) z = (d:ℂ)*field S (d • z) := by
  unfold field
  rw [potential_dilate S hd,fderiv_comp_smul d]
  simp only [smul_apply,Complex.real_smul]
  ring

theorem truncatedDeficit_dilate (S : ℂ → ℂ) {d : ℝ} (hd : 0<d) (R : ℝ) :
    truncatedDeficit (dilateFunction S d) R = truncatedDeficit S (d*R) := by
  let f := fun w => k₀*‖S w‖^2-‖field S w‖^2
  have hm (r : ℝ) : MeasurableSet (halfDisc r) := upper_open.measurableSet.inter Metric.isOpen_ball.measurableSet
  have pre (z : ℂ) : z ∈ halfDisc R ↔ d • z ∈ halfDisc (d*R) := by
    simp [halfDisc,upper,Metric.mem_ball,hd,Complex.real_smul,norm_mul,Complex.norm_of_nonneg hd.le,abs_of_pos hd]
  have h := area_integral_dilate f hd (hm R) (hm (d*R)) pre
  unfold truncatedDeficit
  calc
    _ = ∫ z in halfDisc R, d^2*f (d • z) ∂area := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [dilateFunction,field_dilate S hd,norm_mul,Complex.norm_of_nonneg hd.le,f]
      ring
    _ = _ := by
      rw [integral_const_mul,h,smul_eq_mul,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero 2 hd.ne'),one_mul]

theorem deficit_dilate {S : ℂ → ℂ} (hf : finitePartExists S) {d : ℝ} (hd : 0 < d) :
    deficit (dilateFunction S d) = deficit S := by
  apply Tendsto.limUnder_eq
  change Tendsto (fun R => truncatedDeficit (dilateFunction S d) R) atTop _
  simpa only [truncatedDeficit_dilate S hd,Function.comp_def,id_eq] using
    (finite_part_limit hf).comp (tendsto_id.const_mul_atTop hd)

theorem Pair.dilate_value (p : Pair) {d : ℝ} (hd : 0<d) :
    (p.dilate d hd).value = dilateFunction p.value d := by
  funext z
  simp only [Pair.value,Pair.dilate,dilateFunction,pole,Complex.real_smul,mul_add]
  have h (a : ℝ) (w : ℂ) : -(a:ℂ)/(z-w/(d:ℂ)) = (d:ℂ)*(-(a:ℂ)/((d:ℂ)*z-w)) := by
    rw [show z-w/(d:ℂ) = ((d:ℂ)*z-w)/(d:ℂ) by field_simp [Complex.ofReal_ne_zero.mpr hd.ne']]
    rw [div_div_eq_mul_div]
    ring
  rw [h,h]

theorem Pair.dilate_deficit (p : Pair) (hf : finitePartExists p.value) {d : ℝ} (hd : 0<d) :
    deficit (p.dilate d hd).value = deficit p.value := by
  rw [p.dilate_value hd,deficit_dilate hf hd]

end Liu
