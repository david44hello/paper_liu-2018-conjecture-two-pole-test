module

public import Liu.SupercriticalProjection

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Complex Real
open scoped Topology ContDiff
namespace Liu

/-- Distributional Wirtinger derivative on the open upper half-plane,
paired bilinearly against compactly supported smooth complex tests. -/
def WeakDbar (h f : ℂ → ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ upper →
    (∫ z, h z*dbar φ z ∂upperArea) = -(∫ z, f z*φ z ∂upperArea)

theorem dbar_test_memLp {φ : ℂ → ℂ} (dφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    MemLp (dbar φ) 2 upperArea := by
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  letI : IsFiniteMeasureOnCompacts upperArea := by unfold upperArea; infer_instance
  have H : Continuous (dbar φ) := by
    unfold dbar
    have hd := dφ.continuous_fderiv (by simp)
    fun_prop
  apply H.memLp_of_hasCompactSupport
  have e : tsupport (dbar φ) ⊆ tsupport φ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    exact hx (by simp [dbar,fderiv_of_notMem_tsupport (𝕜:=ℝ) hn])
  exact hc.of_isClosed_subset (isClosed_tsupport _) e

theorem SupercriticalSource.field_weak_dbar {f : ℂ → ℂ} {t : ℝ} (h : SupercriticalSource f t)
    (df : DifferentiableOn ℝ f upper) : WeakDbar (canonicalField f) f := by
  intro φ dφ hc hsub
  let F := canonicalField f
  let H := fun z => F z*φ z
  have hF := canonicalField_continuous h.green.quadratic
  have dF (z : ℂ) (hz : z∈upper) := canonicalField_dbar h.green.quadratic hz (df.differentiableAt (upper_open.mem_nhds hz))
  have hder (z : ℂ) (hz : z∈upper) := (dF z hz).1.hasFDerivAt.mul
    (dφ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hH : DifferentiableOn ℝ H upper := fun z hz => (hder z hz).differentiableAt.differentiableWithinAt
  have hcurl (z : ℂ) (hz : z∈upper) :
      Complex.I*fderiv ℝ H z 1-fderiv ℝ H z Complex.I=
        (2*Complex.I)*(F z*dbar φ z+f z*φ z) := by
    rw [←(dF z hz).2,(show HasFDerivAt H _ z from hder z hz).fderiv]
    dsimp only [F,dbar]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring_nf <;> simp [Complex.I_sq] <;> ring
  have hm := h.field_memLp.integrable_mul (dbar_test_memLp dφ hc)
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous dφ.continuous
  have hi := h.green.integrable.mul_bdd dφ.continuous.aestronglyMeasurable (ae_of_all _ hM)
  have hcH : HasCompactSupport H := hc.mul_left
  obtain ⟨R,_,hR⟩ := hcH.exists_pos_le_norm
  have hz := upper_curl_integral_zero (hF.mul dφ.continuous).continuousOn hH hcurl
    (by intro x; have hn : (x:ℂ)∉tsupport φ := fun hx => by have hh := hsub hx; simpa [upper] using hh
        simp [H,image_eq_zero_of_notMem_tsupport hn])
    ((hm.add hi).const_mul (2*Complex.I)) (b:=fun _ => 0) (by simp)
    (by filter_upwards [eventually_ge_atTop R] with r hr z _ hz; change ‖H z‖≤0; rw [hR z (hr.trans hz),norm_zero])
  erw [integral_const_mul,integral_add hm hi,mul_eq_zero] at hz
  exact eq_neg_of_add_eq_zero_left (hz.resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero))

theorem weak_dbar_difference {f h : ℂ → ℂ} {t : ℝ} (hf : SupercriticalSource f t)
    (df : DifferentiableOn ℝ f upper) (hh : MemLp h 2 upperArea) (hw : WeakDbar h f) :
    WeakDbar (h-canonicalField f) 0 := by
  intro φ dφ hc hs
  have hp := dbar_test_memLp dφ hc
  simp only [Pi.sub_apply,Pi.zero_apply,zero_mul,integral_zero,neg_zero,sub_mul]
  erw [integral_sub (hh.integrable_mul hp) (hf.field_memLp.integrable_mul hp),hw φ dφ hc hs,
    hf.field_weak_dbar df φ dφ hc hs,sub_self]

end Liu
