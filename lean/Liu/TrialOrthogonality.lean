module

public import Liu.TrialIntegral
public import Liu.Denominator

@[expose] public section

noncomputable section
open Set MeasureTheory Complex Real Filter
open scoped Topology ComplexConjugate InnerProductSpace
namespace Liu

private theorem cross_integrable {F G : ℂ → ℂ} (hf : MemLp F 2 upperArea) (hg : MemLp G 2 upperArea) :
    Integrable (fun z => G z*conj (F z)) upperArea := by
  have hc : MemLp (fun z => conj (F z)) 2 upperArea := hf.congr_norm
    (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (ae_of_all _ fun z => (Complex.norm_conj _).symm)
  exact hg.integrable_mul hc

private theorem real_cross {F G : ℂ → ℂ} (hf : MemLp F 2 upperArea) (hg : MemLp G 2 upperArea) :
    (∫ z, (G z*conj (F z)).re ∂upperArea)=(inner ℂ (asL2 F) (asL2 G)).re := by
  apply (integral_re (cross_integrable hf hg)).trans
  apply congrArg Complex.re
  rw [asL2,asL2,dif_pos hf,dif_pos hg,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with z hf' hg'
  rw [hf',hg',RCLike.inner_apply]

section
variable {F G : ℂ → ℂ} {η C : ℝ} (h : TrialWindow F G η C)
include h

theorem TrialWindow.cross_zero (hF : DifferentiableOn ℂ F upper)
    (hG : asL2 G=asL2 (logInput F)-project (asL2 (logInput F))) :
    (∫ z, (G z*conj (F z)).re ∂upperArea)=0 := by
  letI : analyticSubspace.HasOrthogonalProjection := by unfold analyticSubspace; infer_instance
  have hmem : asL2 F ∈ analyticSubspace := by
    rw [asL2,dif_pos h.input]
    exact (Submodule.span ℂ analyticVectors).le_topologicalClosure
      (Submodule.subset_span (show h.input.toLp F ∈ analyticVectors from ⟨F,h.input,hF,rfl⟩))
  have hort : asL2 G ∈ analyticSubspaceᗮ := hG ▸ Submodule.sub_starProjection_mem_orthogonal _
  rw [real_cross h.input h.direction,hort _ hmem]; rfl

omit h in
private theorem TrialWindow.log_cross_point (f g : ℂ) :
    Real.log ‖f‖*(g*conj f).re=(g*conj (f*(Real.log ‖f‖:ℂ))).re := by
  rw [map_mul,Complex.conj_ofReal,←mul_assoc,mul_comm (g*conj f) _,Complex.re_ofReal_mul]

theorem TrialWindow.orthogonal_density_limit (hF : DifferentiableOn ℂ F upper)
    (hlog : MemLp (logInput F) 2 upperArea)
    (hG : asL2 G=asL2 (logInput F)-project (asL2 (logInput F))) :
    Tendsto (fun d => ∫ z, trialDensity (F z) (G z) d ∂upperArea) (𝓝[≠] 0) (𝓝 (-energy G)) := by
  letI : analyticSubspace.HasOrthogonalProjection := by unfold analyticSubspace; infer_instance
  let v := asL2 (logInput F)
  have hort : asL2 G ∈ analyticSubspaceᗮ := hG ▸ Submodule.sub_starProjection_mem_orthogonal _
  have horth : inner ℂ (project v) (asL2 G)=0 := hort _ (analyticSubspace.starProjection_apply_mem _)
  have hi : inner ℂ v (asL2 G) = inner ℂ (asL2 G) (asL2 G) := by
    conv_rhs => lhs; rw [hG]
    rw [inner_sub_left,horth,sub_zero]
  have hw : (∫ z, (G z*conj (logInput F z)).re ∂upperArea) = energy G := by
    rw [real_cross hlog h.direction]
    change (inner ℂ v (asL2 G)).re=_
    rw [hi]; exact inner_self_eq_norm_sq (𝕜:=ℂ) (asL2 G)
  have hc : Integrable (fun z => (G z*conj (F z)).re) upperArea := Complex.reCLM.integrable_comp (cross_integrable h.input h.direction)
  have hl : Integrable (fun z => (G z*conj (logInput F z)).re) upperArea := Complex.reCLM.integrable_comp (cross_integrable hlog h.direction)
  have hs := (memLp_two_iff_integrable_sq_norm h.direction.aestronglyMeasurable).mp h.direction
  have H := h.density_integral_limit
  have he : (∫ z, ‖G z‖^2-(G z*conj (F z)).re-2*Real.log ‖F z‖*(G z*conj (F z)).re ∂upperArea)= -energy G := by
    simp_rw [mul_assoc (2:ℝ),TrialWindow.log_cross_point]
    change (∫ z, ‖G z‖^2-(G z*conj (F z)).re-2*(G z*conj (logInput F z)).re ∂upperArea)=_
    erw [integral_sub (hs.sub hc) (hl.const_mul 2),integral_sub hs hc,integral_const_mul,
      ←energy_eq_integral h.direction,h.cross_zero hF hG,hw]
    ring
  rwa [he] at H

def TrialWindow.trialInput (F G : ℂ → ℂ) (d : ℝ) (z : ℂ) := F z-(d:ℂ)*G z

open TrialWindow

theorem TrialWindow.trial_input_integrable {d : ℝ} (hd : |d|≤η) (h₀ : d≠0) :
    Integrable (fun z => ‖trialInput F G d z‖^(2+d)) upperArea := by
  have hc : Integrable (fun z => (G z*conj (F z)).re) upperArea := Complex.reCLM.integrable_comp (cross_integrable h.input h.direction)
  have hint := (((h.density_integrable hd).const_mul (d^2)).add (h.power_integrable hd)).sub (hc.const_mul (2*d))
  apply hint.congr
  filter_upwards with z
  change d^2*trialDensity (F z) (G z) d+‖F z‖^(2+d)-2*d*(G z*conj (F z)).re=_
  unfold trialDensity trialInput
  field_simp
  <;> ring

theorem TrialWindow.trial_difference_limit (hF : DifferentiableOn ℂ F upper)
    (hlog : MemLp (logInput F) 2 upperArea)
    (hG : asL2 G=asL2 (logInput F)-project (asL2 (logInput F))) :
    Tendsto (fun d : ℝ => ((∫ z, ‖trialInput F G d z‖^(2+d) ∂upperArea)-
      ∫ z, ‖F z‖^(2+d) ∂upperArea)/d^2) (𝓝[≠] 0) (𝓝 (-energy G)) := by
  apply (h.orthogonal_density_limit hF hlog hG).congr'
  filter_upwards [h.near_window,self_mem_nhdsWithin] with d hd (hd₀ : d≠0)
  have hc : Integrable (fun z => (G z*conj (F z)).re) upperArea := Complex.reCLM.integrable_comp (cross_integrable h.input h.direction)
  change (∫ z, ((‖trialInput F G d z‖^(2+d)-‖F z‖^(2+d))+2*d*(G z*conj (F z)).re)/d^2 ∂upperArea)=_
  erw [integral_div,integral_add ((h.trial_input_integrable hd hd₀).sub (h.power_integrable hd)) (hc.const_mul (2*d)),
    integral_sub (h.trial_input_integrable hd hd₀) (h.power_integrable hd),integral_const_mul,h.cross_zero hF hG]
  ring

end
end Liu
