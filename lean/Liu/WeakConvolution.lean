module

public import Liu.WeakPrimitive
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

@[expose] public section

noncomputable section
open Set MeasureTheory Filter Complex Function
open scoped Topology ContDiff Convolution
namespace Liu

/-- Test the unscaled whole-plane representative on smooth compact tests
contained in the open upper half-plane. -/
def upperWeakZero (f : ℂ → ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ⊆upper →
    (∫ w, f w*dbar φ w)=0

theorem lower_kernel_smoothing {f K : ℂ → ℂ}
    (hf : LocallyIntegrable f volume) (hw : upperWeakZero f)
    (hd : ContDiff ℝ ∞ K) (hc : HasCompactSupport K) (hK : ∀ w∈tsupport K, w.im≤0) :
    DifferentiableOn ℂ (f ⋆[ContinuousLinearMap.mul ℝ ℂ,volume] K) upper := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  intro z hz
  let φ := fun w : ℂ => K (z-w)
  have dφ : ContDiff ℝ ∞ φ := hd.comp (contDiff_const.sub contDiff_id)
  have hφ : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.subLeft z)
  have hs : tsupport φ⊆upper := by
    have H : tsupport φ ⊆ (fun w : ℂ => z-w) ⁻¹' tsupport K :=
      closure_minimal (fun w hw => subset_tsupport K hw) ((isClosed_tsupport _).preimage (by fun_prop))
    intro w hw
    have hh := hK _ (H hw)
    change 0<w.im
    change 0<z.im at hz
    rw [Complex.sub_im] at hh
    linarith
  have dh (w : ℂ) : HasFDerivAt φ _ w := (hd.differentiable (by simp)).differentiableAt.hasFDerivAt.comp w
    ((hasFDerivAt_id (𝕜:=ℝ) w).const_sub z)
  have hzero := hw φ dφ hφ hs
  have hφd (w : ℂ) : dbar φ w= -(fderiv ℝ K (z-w) 1+I*fderiv ℝ K (z-w) I)/2 := by
    rw [dbar,(dh w).fderiv]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,ContinuousLinearMap.id_apply,map_neg]
    ring
  let A := fun w : ℂ => f w*fderiv ℝ K (z-w) 1
  let B := fun w : ℂ => f w*fderiv ℝ K (z-w) I
  have HI (v : ℂ) : Integrable (fun w => f w*fderiv ℝ K (z-w) v) volume :=
    (hc.fderiv_apply ℝ v).convolutionExists_right L hf
      (by have hcont := hd.continuous_fderiv (by simp); fun_prop) z
  have he (w : ℂ) : f w*dbar φ w=(-1/2:ℂ)*(A w+I*B w) := by rw [hφd]; dsimp only [A,B]; ring
  simp_rw [he] at hzero
  rw [integral_const_mul,integral_add (HI 1) ((HI I).const_mul I),integral_const_mul] at hzero
  have hcomb := (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  have H := hc.hasFDerivAt_convolution_right L hf (hd.of_le (by simp)) z
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨H.differentiableAt,?_⟩
  rw [H.fderiv,convolution_precompR_apply L hf (hc.fderiv ℝ) (hd.continuous_fderiv (by simp)),
    convolution_precompR_apply L hf (hc.fderiv ℝ) (hd.continuous_fderiv (by simp))]
  change (∫ w, B w)=I*(∫ w, A w)
  have heq : (∫ w, A w) = -(I*(∫ w, B w)) := eq_neg_of_add_eq_zero_left hcomb
  rw [heq,mul_neg,←mul_assoc,Complex.I_mul_I,neg_one_mul,neg_neg]

end Liu
