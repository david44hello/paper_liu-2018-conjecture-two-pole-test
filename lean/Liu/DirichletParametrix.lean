module

public import Liu.CompactDirichletField
public import Liu.RegularKernelBounds

@[expose] public section

noncomputable section
open Set Filter Metric MeasureTheory Real Complex InnerProductSpace
open scoped ContDiff Topology ComplexConjugate
namespace Liu

private theorem compact_singular_integrable {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper)
    (hc : HasCompactSupport V) (z : ℂ) (hz : z∈closedUpper) :
    Integrable (fun w => greenResolvent z w*V w) upperArea := by
  classical
  let f := upper.indicator V
  have hin : upper⊆closedUpper := fun w hw => (show 0<w.im from hw).le
  have hm : Measurable f := (h.continuousOn.mono hin).measurable_piecewise (continuousOn_const (c:=(0:ℂ))) upper_open.measurableSet
  obtain ⟨C,hC,hb⟩ := compact_weight_bound h.continuousOn hc 2
  have H := (resolvent_source_integrable hm hC (fun w hw => by simpa only [f,indicator_of_mem hw,Real.rpow_two] using hb w (hin hw)) hz).1
  apply H.congr
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
  simp only [f,indicator_of_mem hw]

private theorem compact_parametrix {V : ℂ → ℂ} (hV : ContDiffOn ℝ ∞ V closedUpper)
    (hc : HasCompactSupport V) (hb : ∀ x : ℝ, V x=0) (R : ℝ) (z : ℂ) (hz : z∈closedUpper) :
    let J := fun w => (greenResolvent z w-regularResolvent R z w)*dirLap V w
    let B := fun w => V w*dirLap (regularResolvent R z) w
    Integrable J upperArea ∧ Integrable B upperArea ∧
      dirField V z=(1/2:ℂ)*((∫ w, J w ∂upperArea)+(∫ w, B w ∂upperArea)) := by
  let K := regularResolvent R z
  have hK := (regularResolvent_smooth R z).contDiffOn (s:=closedUpper)
  have hlc : HasCompactSupport (dirLap V) := (dirPart_compact (dirPart_compact hc 1) 1).add (dirPart_compact (dirPart_compact hc I) I)
  have hi := compact_singular_integrable (dirLap_smooth hV) hlc z hz
  have hj : Integrable (fun w => K w*dirLap V w) upperArea :=
    closed_integrable_compact (hK.mul (dirLap_smooth hV)).continuousOn hlc.mul_left
  have hk : Integrable (fun w => V w*dirLap K w) upperArea :=
    closed_integrable_compact (hV.mul (dirLap_smooth hK)).continuousOn hc.mul_right
  dsimp only
  simp only [sub_mul]
  refine ⟨hi.sub hj,hk,?_⟩
  rw [integral_sub hi hj,←dirichlet_green_swap hV hK hc hb (regularResolvent_bottom R z),sub_add_cancel]
  exact compact_dirichlet_field hV hc hb hz

/-- Green's formula with a regularized reciprocal kernel. Each density
on the right vanishes outside the observation ball in the upper half-plane. -/
theorem localized_dirichlet_formula {V : ℂ → ℂ} (hV : ContDiffOn ℝ ∞ V closedUpper)
    (hb : ∀ x : ℝ, V x=0) {R : ℝ} (hR : 0<R) {z : ℂ} (hz : z∈closedUpper) :
    let J := fun w => (greenResolvent z w-regularResolvent R z w)*dirLap V w
    let B := fun w => V w*dirLap (regularResolvent R z) w
    Integrable J upperArea ∧ Integrable B upperArea ∧
      dirField V z=(1/2:ℂ)*((∫ w, J w ∂upperArea)+(∫ w, B w ∂upperArea)) := by
  let b : ContDiffBump z := ⟨2*R,3*R,by positivity,by linarith⟩
  let W := fun w => (b w:ℂ)*V w
  have hW : ContDiffOn ℝ ∞ W closedUpper := (Complex.ofRealCLM.contDiff.comp b.contDiff).contDiffOn.mul hV
  have hc₀ : HasCompactSupport (fun w => (b w:ℂ)) := b.hasCompactSupport.comp_left (by simp : ((0:ℝ):ℂ)=0)
  have hc : HasCompactSupport W := hc₀.mul_right
  have hsame (w : ℂ) (hw : ‖z-w‖≤R) : W=ᶠ[𝓝 w] V := by
    have he : w∈ball z b.rIn := by rw [mem_ball,dist_eq_norm,norm_sub_rev]; change _<2*R; linarith
    filter_upwards [b.eventuallyEq_one_of_mem_ball he] with x hx
    simp [W,show b x=1 from hx]
  have eq := hsame z (by simpa using hR.le)
  have hfield : dirField W z=dirField V z := by
    simp only [dirField,dirPart,(eq.filter_mono nhdsWithin_le_nhds).fderivWithin_eq eq.eq_of_nhds]
  obtain ⟨_,_,H⟩ := regularResolvent_bounds
  have hout := (H R hR z).2.2
  let K := regularResolvent R z
  have hK := (regularResolvent_smooth R z).contDiffOn (s:=closedUpper)
  have eJ : (fun w => (greenResolvent z w-K w)*dirLap W w)=ᵐ[upperArea]
      (fun w => (greenResolvent z w-K w)*dirLap V w) := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
    by_cases hn : ‖z-w‖≤R
    · rw [dirLap_inside hW hw,dirLap_inside hV hw,(laplacian_congr_nhds (hsame w hn)).eq_of_nhds]
    · simp only [K,(hout w hz hw (le_of_not_ge hn)).1,sub_self,zero_mul]
  have eB : (fun w => W w*dirLap K w)=ᵐ[upperArea] (fun w => V w*dirLap K w) := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
    by_cases hn : ‖z-w‖≤R
    · rw [(hsame w hn).eq_of_nhds]
    · rw [dirLap_inside hK hw,(hout w hz hw (le_of_not_ge hn)).2]; simp
  obtain ⟨hi,hj,he⟩ := compact_parametrix hW hc (by intro x; simp [W,hb]) R z hz
  change dirField W z=(1/2:ℂ)*((∫ w, (greenResolvent z w-K w)*dirLap W w ∂upperArea)+(∫ w, W w*dirLap K w ∂upperArea)) at he
  rw [hfield,integral_congr_ae eJ,integral_congr_ae eB] at he
  exact ⟨hi.congr eJ,hj.congr eB,he⟩

end Liu
