import Liu.EdgeTraceL1

noncomputable section
open Set Real MeasureTheory
namespace Liu

def edgeAverage (x y : ℝ) (f : ℝ → ℝ) : ℝ := (∫ X, poissonLine x y X*f X)/π

private theorem poisson_integrable (x : ℝ) {y : ℝ} (hy : 0<y) : Integrable (poissonLine x y) :=
  Integrable.of_integral_ne_zero ((poissonLine_integral x hy) ▸ pi_ne_zero)

private theorem poisson_f_integrable (x : ℝ) {y M : ℝ} (hy : 0<y) {f : ℝ → ℝ}
    (hm : Measurable f) (hf : ∀ X, |f X|≤M) : Integrable (fun X => poissonLine x y X*f X) := by
  apply ((poisson_integrable x hy).mul_const M).mono' (by unfold poissonLine; fun_prop)
  filter_upwards with X
  have hP : 0≤poissonLine x y X := by unfold poissonLine; positivity
  simpa [Real.norm_eq_abs,abs_mul,abs_of_nonneg hP] using mul_le_mul_of_nonneg_left (hf X) hP

theorem edgeAverage_bound (x : ℝ) {y M : ℝ} (hy : 0<y) {f : ℝ → ℝ}
    (hf : ∀ X, |f X|≤M) : |edgeAverage x y f|≤M := by
  rw [edgeAverage,abs_div,abs_of_pos pi_pos,div_le_iff₀ pi_pos,←Real.norm_eq_abs]
  apply (norm_integral_le_of_norm_le ((poisson_integrable x hy).mul_const M) ?_).trans_eq
  · rw [integral_mul_const,poissonLine_integral x hy,mul_comm]
  · filter_upwards with X
    have hP : 0≤poissonLine x y X := by unfold poissonLine; positivity
    simpa [Real.norm_eq_abs,abs_mul,abs_of_nonneg hP] using mul_le_mul_of_nonneg_left (hf X) hP

private theorem average_difference {x₁ x₂ y₁ y₂ M : ℝ} (h₁ : 0<y₁) (h₂ : 0<y₂) {f g : ℝ → ℝ}
    (hm : Measurable f) (hf : ∀ X, |f X|≤M) (hi : Integrable g)
    (hd : ∀ X, |poissonLine x₁ y₁ X-poissonLine x₂ y₂ X|≤g X) :
    |edgeAverage x₁ y₁ f-edgeAverage x₂ y₂ f| ≤ (∫ X, g X)*M/π := by
  rw [edgeAverage,edgeAverage,←sub_div,abs_div,abs_of_pos pi_pos]
  apply div_le_div_of_nonneg_right _ pi_pos.le
  rw [←integral_sub (poisson_f_integrable x₁ h₁ hm hf) (poisson_f_integrable x₂ h₂ hm hf),←integral_mul_const,←Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hi.mul_const M)
  filter_upwards with X
  rw [←sub_mul,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul (hd _) (hf _) (abs_nonneg _) ((abs_nonneg _).trans (hd _))

theorem edgeAverage_space {y M : ℝ} (hy : 0<y) (x x' : ℝ) {f : ℝ → ℝ}
    (hm : Measurable f) (hf : ∀ X, |f X|≤M) :
    |edgeAverage x y f-edgeAverage x' y f|≤M*|x-x'|/y := by
  let g := fun X => (|x-x'|/(2*y))*(poissonLine x y X+poissonLine x' y X)
  have hI : Integrable g := ((poisson_integrable x hy).add (poisson_integrable x' hy)).const_mul _
  have hd (X : ℝ) : |poissonLine x y X-poissonLine x' y X|≤g X := by
    let d := X-x
    let e := X-x'
    have hD : 0<d^2+y^2 := by positivity
    have hE : 0<e^2+y^2 := by positivity
    have he : poissonLine x y X-poissonLine x' y X = (x-x')*(y*(d+e))/((d^2+y^2)*(e^2+y^2)) := by
      change y/(d^2+y^2)-y/(e^2+y^2)=_
      field_simp [hD.ne',hE.ne']; dsimp [d,e]; ring
    have hb : |y*(d+e)|≤(d^2+e^2+2*y^2)/2 := abs_le.mpr ⟨by nlinarith only [sq_nonneg (d+y),sq_nonneg (e+y)],
      by nlinarith only [sq_nonneg (d-y),sq_nonneg (e-y)]⟩
    rw [he,abs_div,abs_mul,abs_of_pos (mul_pos hD hE)]
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) (mul_pos hD hE).le).trans_eq
    change _=|x-x'|/(2*y)*(y/(d^2+y^2)+y/(e^2+y^2))
    field_simp [hD.ne',hE.ne',hy.ne'] <;> ring
  apply (average_difference hy hy hm hf hI hd).trans_eq
  unfold g
  rw [integral_const_mul,integral_add (poisson_integrable x hy) (poisson_integrable x' hy),
    poissonLine_integral x hy,poissonLine_integral x' hy]
  field_simp [pi_ne_zero,hy.ne'] <;> ring

theorem edgeAverage_height {a b M : ℝ} (ha : 0<a) (hab : a≤b) (x : ℝ) {f : ℝ → ℝ}
    (hm : Measurable f) (hf : ∀ X, |f X|≤M) :
    |edgeAverage x a f-edgeAverage x b f|≤M*(b-a)/a := by
  have hb := ha.trans_le hab
  let g := fun X => ((b-a)/a)*poissonLine x a X
  have hI : Integrable g := (poisson_integrable x ha).const_mul _
  have hd (X : ℝ) : |poissonLine x a X-poissonLine x b X|≤g X := by
    let v := (X-x)^2
    have hv : 0≤v := sq_nonneg _
    have hD : 0<v+a^2 := by positivity
    have hE : 0<v+b^2 := by positivity
    have he : poissonLine x a X-poissonLine x b X=(b-a)*(a*b-v)/((v+a^2)*(v+b^2)) := by
      change a/(v+a^2)-b/(v+b^2)=_
      field_simp [hD.ne',hE.ne']; ring
    have hab' := mul_le_mul_of_nonneg_right hab hb.le
    have hbnd : |a*b-v|≤v+b^2 := abs_le.mpr ⟨by nlinarith [mul_nonneg ha.le hb.le,sq_nonneg b],by nlinarith⟩
    rw [he,abs_div,abs_mul,abs_of_nonneg (sub_nonneg.mpr hab),abs_of_pos (mul_pos hD hE)]
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbnd (sub_nonneg.mpr hab)) (mul_pos hD hE).le).trans_eq
    change _=(b-a)/a*(a/(v+a^2))
    field_simp [hD.ne',hE.ne',ha.ne']
  apply (average_difference ha hb hm hf hI hd).trans_eq
  unfold g
  rw [integral_const_mul,poissonLine_integral x ha]
  field_simp [pi_ne_zero,ha.ne'] <;> ring

end Liu
