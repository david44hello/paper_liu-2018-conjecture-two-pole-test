import Liu.CauchyDerivative
import Liu.ClosedGreen
import Liu.ArgumentSource
import Liu.Witness
import Mathlib.Analysis.Complex.Conformal

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology ComplexConjugate
namespace Liu

def canonicalField (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  cauchyTransform f z-conj (cauchyTransform (fun w => conj (f w)) (conj z))

theorem canonicalField_continuous {f : ℂ → ℂ} (hf : QuadraticDecay f) : Continuous (canonicalField f) :=
  (cauchyTransform_continuous hf).sub (Complex.continuous_conj.comp ((cauchyTransform_continuous hf.conjugate).comp Complex.continuous_conj))

theorem canonicalField_eq_integral {f : ℂ → ℂ} (hf : QuadraticDecay f) (z : ℂ) :
    canonicalField f z=-(∫ w, greenResolvent z w*f w ∂upperArea) := by
  have hi := cauchyTransform_integrable hf z
  have hj := cauchyTransform_integrable hf.conjugate (conj z)
  have hcon : Integrable (fun w => conj (conj (f w)/(conj z-w))) upperArea :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hj
  unfold canonicalField cauchyTransform
  rw [←integral_conj,←integral_sub hi hcon,←integral_neg]
  apply integral_congr_ae
  filter_upwards with w
  simp [greenResolvent,map_div₀,div_eq_mul_inv]; ring

theorem reflected_cauchy_differentiable {f : ℂ → ℂ} (hf : QuadraticDecay f) {z : ℂ} (hz : z∈upper) :
    DifferentiableAt ℂ (fun x => conj (cauchyTransform (fun w => conj (f w)) (conj x))) z := by
  obtain ⟨K,hK,h⟩ := hf.bound
  have hy : 0<z.im := hz
  have hm := hf.measurable
  have hq : QuadraticDecay (fun w => conj (f w)/(conj z-w)) := by
    refine ⟨by fun_prop, K/z.im,by positivity,?_⟩
    intro w hw
    have hg := Complex.abs_im_le_norm (conj z-w)
    rw [Complex.sub_im,Complex.conj_im,show -z.im-w.im=-(z.im+w.im) by ring,abs_neg,abs_of_pos (add_pos hy hw)] at hg
    have hden : z.im ≤ ‖conj z-w‖ := by change 0<w.im at hw; linarith
    rw [norm_div,Complex.norm_conj]
    apply (div_le_div₀ (by positivity : 0≤K/(1+‖w‖)^2) (h w hw) hy hden).trans_eq
    ring
  have hder := (cauchyTransform_hasDerivAt_of_quotient hf.conjugate hq).differentiableAt.conj_conj
  simpa only [Function.comp_def,Complex.conj_conj] using hder

private theorem remove_dbar_affine {h : ℂ → ℂ} {z b : ℂ} (hd : DifferentiableAt ℝ h z) (hb : dbar h z=b) :
    DifferentiableAt ℂ (fun x => h x-b*conj (x-z)) z := by
  have dc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z ((hasFDerivAt_id (𝕜:=ℝ) z).sub_const z)
  have dh := hd.hasFDerivAt.sub (dc.const_mul b)
  change HasFDerivAt (fun x => h x-b*conj (x-z)) _ z at dh
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨dh.differentiableAt,?_⟩
  rw [dh.fderiv,←hb]
  simp only [dbar,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,Complex.conjCLE_apply,
    ContinuousLinearEquiv.coe_coe,Complex.conj_I,map_one,smul_eq_mul,mul_one]
  ring_nf <;> simp [Complex.I_sq] <;> ring

/-- A local Wirtinger primitive differs from the canonical field by a holomorphic
function. Smoothness of the source is required only at the observation point. -/
theorem canonicalField_holomorphic_difference {f h : ℂ → ℂ} (hf : QuadraticDecay f)
    {z : ℂ} (hz : z∈upper) (hdf : DifferentiableAt ℝ f z) (hdh : DifferentiableAt ℝ h z) (hb : dbar h z=f z) :
    DifferentiableAt ℂ (fun x => h x-canonicalField f x) z := by
  have h1 := remove_dbar_affine hdh hb
  have h2 := cauchyTransform_local_decomposition hf hz hdf
  have h3 := reflected_cauchy_differentiable hf hz
  convert (h1.sub h2).add h3 using 1
  funext w
  simp only [Pi.add_apply,Pi.sub_apply,canonicalField]; ring

theorem PickSum.source_quadratic {n : ℕ} (p : PickSum n) : QuadraticDecay (source p.value) := by
  have hK : 0≤p.derivativeBound/2 := by simpa using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  exact ⟨p.source_measurable,_,hK,fun w hw => p.source_decay (le_of_lt hw)⟩

theorem PickSum.field_eq_canonical {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0≤z.im) :
    field p.value z=canonicalField (source p.value) z :=
  (p.field_integral_closed hz).2.trans (canonicalField_eq_integral p.source_quadratic z).symm

theorem PickSum.field_continuous_closed {n : ℕ} (p : PickSum n) :
    ContinuousOn (field p.value) {z : ℂ | 0≤z.im} :=
  (canonicalField_continuous p.source_quadratic).continuousOn.congr (fun _ hz => p.field_eq_canonical hz)

theorem PickSum.optimalWitness_holomorphic {n : ℕ} (p : PickSum n) :
    DifferentiableOn ℂ (optimalWitness p.value) upper := by
  intro z hz
  have hn : p.value z≠0 := fun he => by have hh := p.value_im_pos (le_of_lt hz); simp [he] at hh
  have hp := (p.hasDerivAt (le_of_lt hz)).differentiableAt
  have hlog := hp.clog (Complex.mem_slitPlane_iff.mpr (Or.inr (p.value_im_pos (le_of_lt hz)).ne'))
  have harg := Complex.imCLM.differentiableAt.comp z (hlog.restrictScalars ℝ)
  have harg' : DifferentiableAt ℝ (fun w => (p.value w).arg) z := by
    simpa only [Function.comp_def,Complex.imCLM_apply,Complex.log_im] using harg
  have hfun : DifferentiableAt ℝ (fun x => p.value x*(Complex.arg (p.value x):ℂ)) z := by
    exact (hp.restrictScalars ℝ).mul (Complex.ofRealCLM.differentiableAt.comp z harg')
  have hdr := (p.holomorphic.deriv upper_open).differentiableAt (upper_open.mem_nhds hz)
  have hstar {a : ℂ → ℂ} (hd : DifferentiableAt ℂ a z) :
      DifferentiableAt ℝ (fun w => conj (a w)) z := Complex.conjCLE.differentiableAt.comp z (hd.restrictScalars ℝ)
  have hsrc : DifferentiableAt ℝ (source p.value) z := by
    unfold source
    have hpr : DifferentiableAt ℝ p.value z := hp.restrictScalars ℝ
    have hcp : DifferentiableAt ℝ (fun w => conj (p.value w)) z := hstar hp
    have hrat : DifferentiableAt ℝ (fun w => p.value w/conj (p.value w)) z := by
      simpa only [div_eq_mul_inv,Pi.mul_def,Pi.inv_def] using hpr.mul (hcp.inv ((map_ne_zero (starRingEnd ℂ)).mpr hn))
    exact (hrat.const_mul (Complex.I/2)).mul (hstar hdr)
  have hd := canonicalField_holomorphic_difference p.source_quadratic hz hsrc hfun (p.argument_source_identity (le_of_lt hz))
  apply (hd.div hp hn).differentiableWithinAt.congr
  · intro w hw; simp [optimalWitness,p.field_eq_canonical (le_of_lt hw)]
  · simp [optimalWitness,p.field_eq_canonical (le_of_lt hz)]

end Liu
