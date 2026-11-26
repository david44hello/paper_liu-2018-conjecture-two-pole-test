import Liu.GreenInterior
import Liu.BoundaryField

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

theorem PickSum.potential_hasFDerivAt {n : ℕ} (p : PickSum n) {z : ℂ} (hz : z∈upper) :
    HasFDerivAt (potential p.value) (greenDifferential (source p.value) z) z := by
  have hK : 0≤p.derivativeBound/2 := by simpa using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  exact reflectedPotential_hasFDerivAt p.source_measurable hK (fun _ hw => p.source_decay (le_of_lt hw))
    (fun _ hw => p.potential_integrable hw) hz

theorem PickSum.potential_differentiable_closed {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0≤z.im) :
    DifferentiableAt ℝ (potential p.value) z := by
  rcases hz.eq_or_lt with he | hi
  · have h : z=(z.re:ℂ) := by apply Complex.ext <;> simp [←he]
    rw [h]
    exact (p.potential_hasFDerivAt_boundary _).differentiableAt
  · exact (p.potential_hasFDerivAt hi).differentiableAt

/-- Absolutely convergent Cauchy-kernel formula for the physical field at
each interior point. Its real derivative comes from the actual Green potential. -/
theorem PickSum.field_integral {n : ℕ} (p : PickSum n) {z : ℂ} (hz : z∈upper) :
    Integrable (fun w => greenResolvent z w*source p.value w) upperArea ∧
    field p.value z = -(∫ w, greenResolvent z w*source p.value w ∂upperArea) := by
  have hK : 0≤p.derivativeBound/2 := by simpa using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  obtain ⟨h,hi,hj⟩ := resolvent_source_integrable p.source_measurable hK (fun _ hw => p.source_decay (le_of_lt hw)) (le_of_lt hz)
  refine ⟨h,?_⟩
  rw [field,(p.potential_hasFDerivAt hz).fderiv]
  simp only [greenDifferential,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply,Complex.imCLM_apply,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,
    one_smul,zero_smul,sub_zero,zero_sub,mul_neg,sub_neg_eq_add]
  rw [←integral_const_mul,←integral_add hi (hj.const_mul Complex.I)]
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  calc
    _ = (((greenResolvent z w).re:ℂ)+((greenResolvent z w).im:ℂ)*Complex.I)*source p.value w := by ring
    _ = _ := by rw [Complex.re_add_im]

end Liu
