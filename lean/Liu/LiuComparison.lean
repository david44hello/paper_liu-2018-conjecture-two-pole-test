import Liu.TrialComparison

noncomputable section
open Set Filter MeasureTheory Real Complex
open scoped Topology ENNReal
namespace Liu

/-- Proposition 3.1. The norm is the sharp norm of the actual upper-half-plane
Bergman integral on Lp. The direction in the pointwise bound is the Hilbert
orthogonal residual of the logarithmic input. -/
theorem liu_norm_comparison {F : ℂ → ℂ}
    (hF : MemLp F 2 upperArea) (hhol : DifferentiableOn ℂ F upper)
    (hn : ∀ z ∈ upper, F z≠0) {η₀ C : ℝ} (hη : 0<η₀) (hC : 0<C)
    (hm : ∀ p : ℝ, |p-2|≤η₀ →
      Integrable (fun z => ‖F z‖^p*(1+|Real.log ‖F z‖|)^5) upperArea)
    (hg : ∀ᵐ z ∂upperArea, ‖(asL2 (logInput F)-project (asL2 (logInput F))) z‖ ≤
      C*‖F z‖*(1+|Real.log ‖F z‖|)) :
    (∀ p : ℕ → ℝ, Tendsto p atTop (𝓝 2) → (∀ n, p n≠2) →
      (∀ n, bergmanLpNorm (p n)≤ENNReal.ofReal (liuNorm (p n))) → quotient F≤k₀) ∧
    (k₀<quotient F → ∀ᶠ p in 𝓝[≠] (2:ℝ), ENNReal.ofReal (liuNorm p)<bergmanLpNorm p) := by
  let v := asL2 (logInput F)-project (asL2 (logInput F))
  let G : ℂ → ℂ := ⇑v
  have hG : MemLp G 2 upperArea := Lp.memLp v
  have heq : asL2 G=v := by rw [asL2,dif_pos hG]; exact Lp.toLp_coeFn _ _
  have hlog : MemLp (logInput F) 2 upperArea := by
    have hf := hF.aestronglyMeasurable.aemeasurable
    have hm' := hm 2 (by simpa using hη.le)
    have hl : AEMeasurable (logInput F) upperArea := by unfold logInput; fun_prop
    apply (memLp_two_iff_integrable_sq_norm hl.aestronglyMeasurable).mpr
    apply hm'.mono' ((hl.norm.pow_const (2:ℕ)).aestronglyMeasurable)
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖logInput F z‖)]
    simp only [logInput,norm_mul,Complex.norm_real,Real.norm_eq_abs,Real.rpow_two,mul_pow]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have h₁ : 1≤1+|Real.log ‖F z‖| := by linarith [abs_nonneg (Real.log ‖F z‖)]
    exact (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |Real.log ‖F z‖|≤1+|Real.log ‖F z‖|) 2).trans
      (pow_le_pow_right₀ h₁ (by decide))
  let η := min η₀ 1
  have hpos : 0<η := lt_min hη zero_lt_one
  have hne : ∀ᵐ z ∂upperArea, F z≠0 := (ae_restrict_mem (μ:=area) upper_open.measurableSet).mono hn
  have hr : ∀ᵐ z ∂upperArea, ‖G z/F z‖≤C*(1+|Real.log ‖F z‖|) := by
    filter_upwards [hne,hg] with z hz hb
    rw [norm_div,div_le_iff₀ (norm_pos_iff.mpr hz)]
    exact hb.trans_eq (by ring)
  have hw : TrialWindow F G η C := ⟨hpos,min_le_right ..,hC.le,hF,hG,hne,hr,
    hm _ (by rw [show 2-η-2= -η by ring,abs_neg,abs_of_pos hpos]; exact min_le_left ..),
    hm _ (by rw [show 2+η-2=η by ring,abs_of_pos hpos]; exact min_le_left ..)⟩
  have near (hq : k₀<quotient F) :
      ∀ᶠ p in 𝓝[≠] (2:ℝ), ENNReal.ofReal (liuNorm p)<bergmanLpNorm p := by
    have H := hw.comparison_near_two hhol hlog heq hq
    have ht : Tendsto (fun p : ℝ => p-2) (𝓝[≠] 2) (𝓝 0) := by
      simpa using (show Tendsto (fun p : ℝ => p) (𝓝[≠] 2) (𝓝 2) from nhdsWithin_le_nhds).sub_const 2
    have ht' : Tendsto (fun p : ℝ => p-2) (𝓝[≠] 2) (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr
      ⟨ht,(show ∀ᶠ p : ℝ in 𝓝[≠] 2, p≠2 from self_mem_nhdsWithin).mono fun p (hp : p≠2) => sub_ne_zero.mpr hp⟩
    filter_upwards [ht'.eventually H] with p hp
    simpa only [add_sub_cancel] using hp
  refine ⟨?_,near⟩
  intro p hp hn hb
  by_contra! hq
  have ht : Tendsto p atTop (𝓝[≠] 2) := tendsto_nhdsWithin_iff.mpr ⟨hp,.of_forall hn⟩
  obtain ⟨n,hn'⟩ := (ht.eventually (near hq)).exists
  exact (not_lt_of_ge (hb n)) hn'

end Liu
