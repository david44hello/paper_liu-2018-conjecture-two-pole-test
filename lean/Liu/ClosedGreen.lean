module

public import Liu.FieldIntegral
public import Liu.TraceSlices

@[expose] public section

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

theorem greenResolvent_boundary (x : ℝ) (w : ℂ) :
    greenResolvent (x:ℂ) w = -Complex.I*((2*w.im/‖w-(x:ℂ)‖^2:ℝ):ℂ) := by
  have he : ((x:ℂ)-conj w)⁻¹ = conj (((x:ℂ)-w)⁻¹) := by simp
  have hs (v : ℂ) : conj v-v=-((2*v.im:ℝ):ℂ)*Complex.I := by
    rw [←neg_sub,Complex.sub_conj]; ring
  rw [greenResolvent,he,hs,Complex.inv_im,Complex.sub_im,Complex.ofReal_im,zero_sub,neg_neg,←Complex.sq_norm,norm_sub_rev (x:ℂ) w]
  push_cast; ring

theorem PickSum.greenDifferential_boundary {n : ℕ} (p : PickSum n) (x : ℝ) :
    greenDifferential (source p.value) x = Complex.imCLM.smulRight (poissonTrace p.value x) := by
  ext h
  have hK : 0≤p.derivativeBound/2 := by simpa using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  rw [greenDifferential_apply p.source_measurable hK (fun _ hw => p.source_decay (le_of_lt hw)) (by simp)]
  simp only [ContinuousLinearMap.smulRight_apply,Complex.imCLM_apply,Complex.real_smul]
  change _=(h.im:ℂ)*(∫ w, traceDensity p.value x w ∂upperArea)
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  rw [greenResolvent_boundary]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,traceDensity]
  push_cast; ring

theorem PickSum.potential_hasFDerivAt_closed {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0≤z.im) :
    HasFDerivAt (potential p.value) (greenDifferential (source p.value) z) z := by
  rcases hz.eq_or_lt with he | hi
  · have h : z=(z.re:ℂ) := by apply Complex.ext <;> simp [←he]
    rw [h,p.greenDifferential_boundary]
    exact p.potential_hasFDerivAt_boundary _
  · exact p.potential_hasFDerivAt hi

theorem PickSum.field_integral_closed {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0≤z.im) :
    Integrable (fun w => greenResolvent z w*source p.value w) upperArea ∧
    field p.value z = -(∫ w, greenResolvent z w*source p.value w ∂upperArea) := by
  rcases hz.eq_or_lt with he | hi
  · have h : z=(z.re:ℂ) := by apply Complex.ext <;> simp [←he]
    rw [h]
    have q : (fun w => greenResolvent (z.re:ℂ) w * source p.value w) = fun w => -Complex.I*traceDensity p.value z.re w := by
      funext w; rw [greenResolvent_boundary,traceDensity,mul_assoc]
    rw [q]
    refine ⟨(p.traceDensity_integrable _).const_mul _,?_⟩
    rw [p.field_on_boundary,integral_const_mul,neg_mul,neg_neg]; rfl
  · exact p.field_integral hi

end Liu
