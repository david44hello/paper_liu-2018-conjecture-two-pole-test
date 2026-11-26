import Liu.TrialOrthogonality
import Liu.BergmanLpNorm

noncomputable section
open Set Filter MeasureTheory Real Complex
open scoped Topology ENNReal
namespace Liu.TrialWindow

variable {F G : ℂ → ℂ} {η C : ℝ} (h : TrialWindow F G η C)
include h

theorem kernel_trial (d : ℝ) (hF : DifferentiableOn ℂ F upper)
    (hG : asL2 G=asL2 (logInput F)-project (asL2 (logInput F))) :
    bergmanIntegral (trialInput F G d)=ᵐ[upperArea] F := by
  letI : analyticSubspace.HasOrthogonalProjection := by unfold analyticSubspace; infer_instance
  have hz : project (asL2 G)=0 := by
    have hv : project (asL2 (logInput F))∈analyticSubspace := analyticSubspace.starProjection_apply_mem _
    have he : project (project (asL2 (logInput F)))=project (asL2 (logInput F)) :=
      Submodule.starProjection_eq_self_iff.mpr hv
    rw [hG,map_sub,he,sub_self]
  have hm : MemLp (trialInput F G d) 2 upperArea := h.input.sub (h.direction.const_smul (d:ℂ))
  have heq : hm.toLp (trialInput F G d) = h.input.toLp F-(d:ℂ) • h.direction.toLp G := by
    exact (MemLp.toLp_sub h.input (h.direction.const_smul (d:ℂ))).trans
      (by rw [MemLp.toLp_const_smul])
  have hp : project (hm.toLp (trialInput F G d))=h.input.toLp F := by
    rw [asL2,dif_pos h.direction] at hz
    rw [heq,map_sub,map_smul,project_fixes_analytic h.input hF,hz,smul_zero,sub_zero]
  obtain ⟨g,hg,_,hproj,hpoint⟩ := projection_has_kernel hm
  have H : hg.toLp g=h.input.toLp F := hproj.symm.trans hp
  have he := hg.coeFn_toLp.symm.trans (H ▸ h.input.coeFn_toLp)
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,he] with z hz he
  exact (hpoint hz).symm.trans he

theorem op_trial_inequality {d : ℝ} (hd : |d|≤η) (hd₀ : d≠0) (hp : 1<2+d)
    (hF : DifferentiableOn ℂ F upper)
    (hG : asL2 G=asL2 (logInput F)-project (asL2 (logInput F)))
    (hB : bergmanLpNorm (2+d) ≤ ENNReal.ofReal (liuNorm (2+d))) :
    (∫ z, ‖F z‖^(2+d) ∂upperArea)≤liuNorm (2+d)^(2+d)*(∫ z, ‖trialInput F G d z‖^(2+d) ∂upperArea) := by
  have hp₀ : 0<2+d := by linarith
  have makeLp {f : ℂ → ℂ} (hm : AEStronglyMeasurable f upperArea)
      (hi : Integrable (fun z => ‖f z‖^(2+d)) upperArea) : MemLp f (ENNReal.ofReal (2+d)) upperArea := by
    apply (integrable_norm_rpow_iff hm (by simpa using hp₀) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hp₀.le] using hi
  exact bergmanLpNorm_power_bound hp hB
    (makeLp (h.input.sub (h.direction.const_smul (d:ℂ))).aestronglyMeasurable (h.trial_input_integrable hd hd₀))
    (makeLp h.input.aestronglyMeasurable (h.power_integrable hd)) (h.kernel_trial d hF hG)

theorem comparison_near_two (hF : DifferentiableOn ℂ F upper)
    (hlog : MemLp (logInput F) 2 upperArea)
    (hG : asL2 G=asL2 (logInput F)-project (asL2 (logInput F)))
    (hQ : k₀<quotient F) :
    ∀ᶠ d : ℝ in 𝓝[≠] 0, ENNReal.ofReal (liuNorm (2+d))<bergmanLpNorm (2+d) := by
  let N := fun d : ℝ => ∫ z, ‖trialInput F G d z‖^(2+d) ∂upperArea
  let M := fun d : ℝ => ∫ z, ‖F z‖^(2+d) ∂upperArea
  have hE : 0<energy F := by
    haveI : NeZero upperArea := ⟨upperArea_ne_zero⟩
    have hx : asL2 F≠0 := by
      rw [asL2,dif_pos h.input]
      intro eq
      have h₀ : F=ᵐ[upperArea] 0 := h.input.coeFn_toLp.symm.trans (eq ▸ Lp.coeFn_zero ℂ 2 upperArea)
      obtain ⟨z,hn,he⟩ := (h.nonzero.and h₀).exists
      exact hn he
    exact sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hq : k₀*energy F-energy G<0 := by
    have hq : k₀ < energy G/energy F := by simpa only [quotient,energy,hG] using hQ
    linarith [(lt_div_iff₀ hE).mp hq]
  let L := 𝓝[≠] (0:ℝ)
  have hd : Tendsto (fun d : ℝ => d) L (𝓝 0) := nhdsWithin_le_nhds
  have hD : Tendsto (fun d : ℝ => (N d-M d)/d^2) L (𝓝 (-energy G)) := h.trial_difference_limit hF hlog hG
  have hN : Tendsto N L (𝓝 (energy F)) := by
    have H := ((hD.mul (hd.pow 2)).add h.power_integral_limit)
    simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero,zero_add] at H
    apply H.congr'
    filter_upwards [self_mem_nhdsWithin] with d (hd : d≠0)
    change (N d-M d)/d^2*d^2+M d=N d
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hd),sub_add_cancel]
  have hlim := (liuNorm_power_limit.mul hN).add hD
  have hneg := hlim.eventually (Iio_mem_nhds (by linarith : k₀*energy F + -energy G<0))
  have hp : ∀ᶠ d : ℝ in L, -1<d := hd.eventually (Ioi_mem_nhds (by norm_num))
  filter_upwards [hneg,h.near_window,self_mem_nhdsWithin,hp] with d hn hdw (hdn : d≠0) hd'
  apply lt_of_not_ge
  intro hB
  have hle : M d≤liuNorm (2+d)^(2+d)*N d :=
    h.op_trial_inequality hdw hdn (by linarith) hF hG hB
  change ((liuNorm (2+d)^(2+d)-1)/d^2)*N d+(N d-M d)/d^2<0 at hn
  have he : ((liuNorm (2+d)^(2+d)-1)/d^2)*N d+(N d-M d)/d^2 =
      (liuNorm (2+d)^(2+d)*N d-M d)/d^2 := by ring
  rw [he] at hn
  exact (not_lt_of_ge (div_nonneg (sub_nonneg.mpr hle) (sq_nonneg _))) hn

end Liu.TrialWindow
