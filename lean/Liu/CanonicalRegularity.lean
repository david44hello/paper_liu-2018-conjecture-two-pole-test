module

public import Liu.CanonicalField
public import Liu.GreenPairing

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate
namespace Liu

theorem canonicalField_affine_difference {f : ℂ → ℂ} (hf : QuadraticDecay f)
    {z : ℂ} (hz : z∈upper) (hd : DifferentiableAt ℝ f z) :
    DifferentiableAt ℂ (fun x => canonicalField f x-f z*conj (x-z)) z := by
  have hlocal := cauchyTransform_local_decomposition hf hz hd
  have hrefl := reflected_cauchy_differentiable hf hz
  convert hlocal.sub hrefl using 1
  funext w; simp only [Pi.sub_apply,canonicalField]; ring

theorem canonicalField_dbar {f : ℂ → ℂ} (hf : QuadraticDecay f)
    {z : ℂ} (hz : z∈upper) (hd : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (canonicalField f) z ∧ dbar (canonicalField f) z=f z := by
  let H := fun x => canonicalField f x-f z*conj (x-z)
  have hH : DifferentiableAt ℂ H z := canonicalField_affine_difference hf hz hd
  have da := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z ((hasFDerivAt_id (𝕜:=ℝ) z).sub_const z)).const_mul (f z)
  have hs := hH.hasDerivAt.complexToReal_fderiv.add da
  have he : (fun w => H w+f z*conj (w-z))=canonicalField f := by funext w; dsimp [H]; ring
  change HasFDerivAt (fun w => H w+f z*conj (w-z)) _ z at hs
  rw [he] at hs
  refine ⟨hs.differentiableAt,?_⟩
  rw [dbar,hs.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.id_apply,Complex.conjCLE_apply,ContinuousLinearEquiv.coe_coe,
    smul_eq_mul,Complex.conj_I,map_one,mul_one]
  ring_nf <;> simp [Complex.I_sq] <;> ring

theorem canonicalField_from_differential {f : ℂ → ℂ} (hf : QuadraticDecay f)
    {z : ℂ} (hz : 0≤z.im) :
    canonicalField f z= -(greenDifferential f z 1-Complex.I*greenDifferential f z Complex.I) := by
  obtain ⟨K,hK,hs⟩ := hf.bound
  obtain ⟨_,hi,hj⟩ := resolvent_source_integrable hf.measurable hK hs hz
  rw [canonicalField_eq_integral hf]
  simp only [greenDifferential,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply,Complex.imCLM_apply,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,
    one_smul,zero_smul,sub_zero,zero_sub,mul_neg,sub_neg_eq_add]
  rw [←integral_const_mul,←integral_add hi (hj.const_mul Complex.I)]
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  calc
    _ = (((greenResolvent z w).re:ℂ)+((greenResolvent z w).im:ℂ)*Complex.I)*f w := by rw [Complex.re_add_im]
    _ = _ := by ring

theorem reflectedPotential_boundary (f : ℂ → ℂ) (x : ℝ) : reflectedPotential f x=0 := by
  unfold reflectedPotential upperArea
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro w hw
  have hh := greenLog_height_bound (z:=(x:ℂ)) (by simp) hw
  have hzero : greenLog x w=0 := abs_nonpos_iff.mp (by simpa using hh)
  simp [hzero]

theorem reflectedPotential_height {f : ℂ → ℂ} (hf : QuadraticDecay f) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → ‖reflectedPotential f z‖ ≤ C*z.im := by
  obtain ⟨K,hK,hs⟩ := hf.bound
  obtain ⟨A,hA,h⟩ := gradientWeight_integral
  refine ⟨2*K*A,by positivity,?_⟩
  intro z hz
  have hg := (h z).1.const_mul (2*z.im*K)
  have hb := norm_integral_le_of_norm_le (f:=fun w => (greenLog z w:ℂ)*f w) hg (by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    apply (mul_le_mul (greenLog_height_bound hz hw) (hs w hw) (norm_nonneg _) (by positivity)).trans
    calc
      _ = (2*z.im*K)*(‖z-w‖⁻¹/(1+‖w‖)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (gradientWeight_majorizes z w) (by positivity))
  apply hb.trans
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (h z).2 (by positivity)).trans_eq (by ring)

theorem reflectedPotential_continuous_closed {f : ℂ → ℂ} (hf : QuadraticDecay f)
    (hi : ∀ z ∈ upper, Integrable (fun w => (greenLog z w:ℂ)*f w) upperArea) :
    ContinuousOn (reflectedPotential f) {z : ℂ | 0≤z.im} := by
  obtain ⟨K,hK,hs⟩ := hf.bound
  intro z hz
  change 0≤z.im at hz
  rcases hz.eq_or_lt with he | hp
  · obtain ⟨C,hC,h⟩ := reflectedPotential_height hf
    have heq : z=(z.re:ℂ) := by apply Complex.ext <;> simp [←he]
    rw [heq]
    unfold ContinuousWithinAt
    rw [reflectedPotential_boundary]
    apply squeeze_zero_norm' (a:=fun w : ℂ => C*w.im) _ (by
      simpa using ((Complex.continuous_im.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).const_mul C : Tendsto _ (𝓝[{w : ℂ | 0≤w.im}] (z.re:ℂ)) _))
    filter_upwards [self_mem_nhdsWithin (a:=(z.re:ℂ)) (s:={w : ℂ | 0≤w.im})] with w hw using h w hw
  · exact (reflectedPotential_hasFDerivAt hf.measurable hK hs hi hp).continuousAt.continuousWithinAt

end Liu
