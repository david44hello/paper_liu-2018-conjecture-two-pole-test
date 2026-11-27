module

public import Liu.FractionalConvolution
public import Liu.DepthFieldComparison
public import Liu.DepthFluxContinuity

@[expose] public section

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped ComplexConjugate Topology
namespace Liu

private theorem cauchy_increment_integral {f : ℂ → ℂ} (hf : QuadraticDecay f) {K C : ℝ} (hK : 0≤K)
    (hdec : ∀ w∈upper, ‖f w‖≤K/(1+‖w‖)^2)
    (hC : ∀ z : ℂ, Integrable (fractionalWeight z) upperArea ∧
      (∫ w, fractionalWeight z w ∂upperArea)≤C/(1+‖z‖)^(5/4:ℝ)) (x y : ℂ) :
    ‖cauchyTransform f x-cauchyTransform f y‖ ≤
      2*K*‖x-y‖^(3/4:ℝ)*(C/(1+‖x‖)^(5/4:ℝ)+C/(1+‖y‖)^(5/4:ℝ)) := by
  let A := 2*K*‖x-y‖^(3/4:ℝ)
  have hA : 0≤A := by dsimp [A]; positivity
  have hI := ((hC x).1.add (hC y).1).const_mul A
  unfold cauchyTransform
  rw [←integral_sub (cauchyTransform_integrable hf x) (cauchyTransform_integrable hf y)]
  apply (norm_integral_le_of_norm_le hI _).trans
  · erw [integral_const_mul,integral_add (hC x).1 (hC y).1]
    exact mul_le_mul_of_nonneg_left (add_le_add (hC x).2 (hC y).2) hA
  · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,upperArea_ae_ne x,upperArea_ae_ne y] with w hw hx hy
    have H := cauchy_increment_bound (sub_ne_zero.mpr (Ne.symm hx)) (sub_ne_zero.mpr (Ne.symm hy))
    rw [sub_sub_sub_cancel_right,norm_sub_rev x w,norm_sub_rev y w] at H
    simp only [div_eq_mul_inv,←mul_sub,norm_mul]
    apply (mul_le_mul (hdec w hw) H (norm_nonneg _) (by positivity)).trans_eq
    dsimp only [A,Pi.add_apply,fractionalWeight]; ring

theorem PickSum.vertical_norm_mono (z : ℂ) {t : ℝ} (hz : 0≤z.im) (ht : 0≤t) :
    ‖z‖≤‖z+(t:ℂ)*Complex.I‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  simp [Complex.sq_norm,Complex.normSq_apply]; nlinarith [mul_nonneg hz ht,sq_nonneg t]

/-- The physical fields of all downward translates of a fixed Pick sum obey
a common spatial Hölder bound that is square integrable in the plane. -/
theorem PickSum.field_increment_weighted {n : ℕ} (p : PickSum n) :
    ∃ B≥0, ∀ u : ℝ, 0≤u → ∀ z : ℂ, 0≤z.im → ∀ h : ℝ, 0≤h →
    ‖field (depthTranslate p.value u) (z+(h:ℂ)*Complex.I)-field (depthTranslate p.value u) z‖
      ≤ B*h^(3/4:ℝ)/(1+‖z‖)^(5/4:ℝ) := by
  obtain ⟨C,hC,H⟩ := fractional_convolution_bound
  let K := p.derivativeBound/2
  have hK : 0≤K := by simpa [K] using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  refine ⟨8*K*C,by positivity,?_⟩
  intro u hu z hz h hh
  let q := p.deeper u hu
  let f := source q.value
  let x := z+(h:ℂ)*Complex.I
  have hx : 0≤x.im := by dsimp [x]; simp; linarith
  have he (w : ℂ) (hw : w∈upper) : ‖f w‖≤K/(1+‖w‖)^2 := by
    dsimp only [f,q]; rw [p.deeper_value hu,source_depthTranslate]
    have hpos : 0≤(w+(u:ℂ)*Complex.I).im := by simp; linarith [show 0<w.im from hw]
    apply (p.source_decay hpos).trans (div_le_div_of_nonneg_left hK (by positivity) _)
    exact pow_le_pow_left₀ (by positivity) (add_le_add (le_refl _) (PickSum.vertical_norm_mono w (le_of_lt hw) hu)) 2
  have hef (w : ℂ) (hw : w∈upper) : ‖conj (f w)‖≤K/(1+‖w‖)^2 := by simpa using he w hw
  have ha := cauchy_increment_integral q.source_quadratic hK he H x z
  have hb := cauchy_increment_integral q.source_quadratic.conjugate hK hef H (conj x) (conj z)
  have hl : ‖x-z‖=h := by simp [x,hh,abs_of_nonneg hh]
  rw [←map_sub,Complex.norm_conj,hl,Complex.norm_conj,Complex.norm_conj] at hb
  rw [hl] at ha
  have hg := div_le_div_of_nonneg_left hC (by positivity : 0<(1+‖z‖)^(5/4:ℝ)) (rpow_le_rpow (by positivity)
    (add_le_add (le_refl 1) (PickSum.vertical_norm_mono z hz hh)) (by norm_num : (0:ℝ)≤5/4))
  have hcoef : 0≤2*K*h^(3/4:ℝ) := by positivity
  have H' := mul_le_mul_of_nonneg_left hg hcoef
  rw [←p.deeper_value hu]
  change ‖field q.value x-field q.value z‖≤_
  rw [q.field_eq_canonical hx,q.field_eq_canonical hz]
  dsimp only [canonicalField]
  rw [show (cauchyTransform f x-conj (cauchyTransform (fun w => conj (f w)) (conj x)))-
      (cauchyTransform f z-conj (cauchyTransform (fun w => conj (f w)) (conj z)))=
      (cauchyTransform f x-cauchyTransform f z)-conj (cauchyTransform (fun w => conj (f w)) (conj x)-
        cauchyTransform (fun w => conj (f w)) (conj z)) by rw [map_sub]; ring]
  apply (norm_sub_le ..).trans
  rw [Complex.norm_conj]
  apply (add_le_add ha hb).trans
  dsimp only [x]; simp only [div_eq_mul_inv] at H' ⊢
  linarith only [H']

/-- Uniform order h^(3/2) for the squared field increment and the cost of
reoptimizing the translated witness. -/
theorem PickSum.depth_increment_energy {n : ℕ} (p : PickSum n) :
    ∃ D≥0, ∀ u : ℝ, ∀ hu : 0≤u, ∀ h : ℝ, ∀ hh : 0≤h,
      let q := p.deeper u hu
      let F := fun z => depthTranslate (field q.value) h z-field q.value z
      MemLp F 2 upperArea ∧ energy F≤D*h^(3/2:ℝ) ∧
      energy (witnessDifference (q.deeper h hh).value (depthTranslate (optimalWitness q.value) h))≤D*h^(3/2:ℝ) := by
  obtain ⟨B,hB,H⟩ := p.field_increment_weighted
  let T := fun z : ℂ => (1+‖z‖)^(-(5/2:ℝ))
  have hT : Integrable T upperArea :=
    ((integrable_one_add_norm (μ:=(volume:Measure ℂ)) (r:=5/2) (by norm_num)).smul_measure
      (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).restrict
  refine ⟨B^2*(∫ z,T z ∂upperArea),mul_nonneg (sq_nonneg _) (integral_nonneg fun z => rpow_nonneg (by positivity) _),?_⟩
  intro u hu h hh
  let q := p.deeper u hu
  let F := fun z => depthTranslate (field q.value) h z-field q.value z
  have hf := field_measurable q.value
  have hm : Measurable F := (hf.comp (measurable_id.add_const ((h:ℂ)*Complex.I))).sub hf
  have hi := hT.const_mul (B^2*h^(3/2:ℝ))
  have hbd : ∀ᵐ z ∂upperArea, ‖F z‖^2≤(B^2*h^(3/2:ℝ))*T z := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    have H' := H u hu z (le_of_lt hz) h hh
    rw [←p.deeper_value hu] at H'
    apply (pow_le_pow_left₀ (norm_nonneg _) H' 2).trans_eq
    have hr : 0<1+‖z‖ := by positivity
    simp only [div_pow,mul_pow,T,←Real.rpow_two (h^(3/4:ℝ)),
      ←Real.rpow_two ((1+‖z‖)^(5/4:ℝ)),←rpow_mul hh,←rpow_mul hr.le]
    norm_num [rpow_neg hr.le,div_eq_mul_inv]
  have hiF : Integrable (fun z => ‖F z‖^2) upperArea := hi.mono' ((hm.norm.pow_const 2).aestronglyMeasurable)
    (hbd.mono fun z hz => by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖F z‖)] using hz)
  have hmem := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hiF
  have hle := integral_mono_ae hiF hi hbd
  rw [←energy_eq_integral hmem,integral_const_mul] at hle
  have he : energy F≤(B^2*(∫ z,T z ∂upperArea))*h^(3/2:ℝ) := by linarith only [hle]
  exact ⟨hmem,he,(q.depth_witness_energy_le hh hmem).trans he⟩

end Liu
