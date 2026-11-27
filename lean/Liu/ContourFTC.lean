module

public import Liu.CutDomain

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Complex Real
open scoped Topology Interval
namespace Liu

/-- Componentwise fundamental theorem for a complex, absolutely continuous path. -/
theorem complex_ac_fundamental {γ : ℝ → ℂ} {a b : ℝ} (h : AbsolutelyContinuousOnInterval γ a b) :
    (∀ᵐ t : ℝ, t∈uIcc a b → DifferentiableAt ℝ γ t) ∧
    IntervalIntegrable (deriv γ) volume a b ∧ (∫ t in a..b,deriv γ t)=γ b-γ a := by
  let X := fun r => (γ r).re
  let Y := fun r => (γ r).im
  have hX : AbsolutelyContinuousOnInterval X a b := reCLM.lipschitz.comp_absolutelyContinuousOnInterval h
  have hY : AbsolutelyContinuousOnInterval Y a b := imCLM.lipschitz.comp_absolutelyContinuousOnInterval h
  let V := fun t => ((deriv X t:ℝ):ℂ)+((deriv Y t:ℝ):ℂ)*I
  have e : γ=fun t => (X t:ℂ)+(Y t:ℂ)*I := by funext t; exact (re_add_im _).symm
  have hd : ∀ᵐ t : ℝ, t∈uIcc a b → HasDerivAt γ (V t) t := by
    filter_upwards [hX.ae_differentiableAt,hY.ae_differentiableAt] with t hx hy ht
    have d := (hx ht).hasDerivAt.ofReal_comp.add ((hy ht).hasDerivAt.ofReal_comp.mul_const I)
    exact e ▸ d
  have cast {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b) :
      IntervalIntegrable (fun t => (f t:ℂ)) volume a b :=
    ⟨hf.1.ofReal,hf.2.ofReal⟩
  have iX := cast hX.intervalIntegrable_deriv
  have iY := cast hY.intervalIntegrable_deriv
  have iV : IntervalIntegrable V volume a b := iX.add (iY.mul_const I)
  have eq : deriv γ =ᵐ[volume.restrict (Ι a b)] V := by
    rw [EventuallyEq,ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hd] with t ht hmem using (ht (uIoc_subset_uIcc hmem)).deriv
  refine ⟨hd.mono (fun t ht hmem => (ht hmem).differentiableAt),(intervalIntegrable_congr_ae eq).mpr iV,?_⟩
  rw [intervalIntegral.integral_congr_ae_restrict eq]
  change (∫ t in a..b,((deriv X t:ℝ):ℂ)+((deriv Y t:ℝ):ℂ)*I)=_
  rw [intervalIntegral.integral_add iX (iY.mul_const I),intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal,intervalIntegral.integral_ofReal,hX.integral_deriv_eq_sub,hY.integral_deriv_eq_sub]
  change ((γ b).re-(γ a).re:ℝ)+(((γ b).im-(γ a).im:ℝ):ℂ)*I=γ b-γ a
  apply Complex.ext <;> simp

theorem analytic_contour_FTC {U : Set ℂ} (ho : IsOpen U) {F f : ℂ → ℂ}
    (hd : ∀ z∈U, HasDerivAt F (f z) z) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hU : MapsTo γ (uIcc a b) U) :
    IntervalIntegrable (fun t => f (γ t)*deriv γ t) volume a b ∧
      (∫ t in a..b, f (γ t)*deriv γ t)=F (γ b)-F (γ a) := by
  let K := γ '' uIcc a b
  have hK : IsCompact K := isCompact_uIcc.image_of_continuousOn hγ.continuousOn
  have hsub : K⊆U := image_subset_iff.mpr hU
  have hF : AnalyticOnNhd ℂ F U :=
    (show DifferentiableOn ℂ F U from fun z hz => (hd z hz).differentiableAt.differentiableWithinAt).analyticOnNhd ho
  have hlip : LocallyLipschitzOn K F := by
    intro z hz
    obtain ⟨k,V,hV,hk⟩ := ((hF z (hsub hz)).contDiffAt (n:=1)).exists_lipschitzOnWith
    exact ⟨k,V,mem_nhdsWithin_of_mem_nhds hV,hk⟩
  obtain ⟨k,hk⟩ := hlip.exists_lipschitzOnWith_of_compact hK
  have hcomp := hk.comp_absolutelyContinuousOnInterval (mapsTo_image γ _) hγ
  obtain ⟨hD,_,_⟩ := complex_ac_fundamental hγ
  obtain ⟨_,hi,he⟩ := complex_ac_fundamental hcomp
  have eq : deriv (F ∘ γ) =ᵐ[volume.restrict (Ι a b)] fun t => f (γ t)*deriv γ t := by
    rw [EventuallyEq,ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hD] with t ht hmem
    have hc := hd (γ t) (hU (uIoc_subset_uIcc hmem))
    have d := hc.scomp t (ht (uIoc_subset_uIcc hmem)).hasDerivAt
    simpa only [smul_eq_mul,mul_comm] using d.deriv
  exact ⟨(intervalIntegrable_congr_ae eq).mp hi,(intervalIntegral.integral_congr_ae_restrict eq).symm.trans he⟩

end Liu
