module

public import Liu.ReciprocalFlux
public import Liu.ReciprocalTail

@[expose] public section

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped Topology
namespace Liu

/-- The reciprocal-depth holomorphic extension of Lemma 6.2. -/
theorem reciprocal_flux_analytic (s γ : ℝ) (hg : γ∈Icc 0 π) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball 0 1) ∧
      ∀ v : ℝ, 0<v → v<1 → G v=((v⁻¹*boundaryFlux (unitDepthSum s γ v):ℝ):ℂ) := by
  let F := topFluxAnalytic s γ
  have hd := topFluxAnalytic_holo s γ
  have h0 : F 0=0 := by
    simpa [F,unitDepth_flux_zero] using topFluxAnalytic_agrees (s:=s) hg (v:=0) le_rfl zero_lt_one
  refine ⟨dslope F 0,((Complex.differentiableOn_dslope (ball_mem_nhds 0 zero_lt_one)).mpr hd).analyticOnNhd isOpen_ball,?_⟩
  intro v hv hv₁
  rw [dslope_of_ne _ (Complex.ofReal_ne_zero.mpr hv.ne'),slope_def_module,h0,sub_zero,sub_zero,smul_eq_mul]
  simp only [F,topFluxAnalytic_agrees hg hv.le hv₁,Complex.ofReal_mul,Complex.ofReal_inv]

theorem reciprocal_flux_extension (s γ : ℝ) (hg : γ∈Icc 0 π) {T : ℝ} (hT : 1<T) :
    topExtension s γ T := by
  obtain ⟨G,hG,he⟩ := reciprocal_flux_analytic s γ hg
  have ht : 0<T := zero_lt_one.trans hT
  have hsub (v : ℝ) (hv : v∈Icc 0 (1/T)) : (v:ℂ)∈ball (0:ℂ) 1 := by
    simp only [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv.1]
    exact hv.2.trans_lt ((div_lt_one ht).mpr hT)
  refine ⟨fun v => (G v).re,?_,?_⟩
  · exact Complex.continuous_re.comp_continuousOn (hG.continuousOn.comp Complex.continuous_ofReal.continuousOn hsub)
  · intro t htt
    have hp := ht.trans_le htt
    have hsmall := (div_lt_one hp).mpr (hT.trans_le htt)
    change t^2*flux s γ t=(G ((1/t:ℝ):ℂ)).re
    rw [he (1/t) (one_div_pos.mpr hp) hsmall,Complex.ofReal_re,reciprocal_flux_scaling s γ hp]

/-- All three assertions, including the real angular extension up to π and
the bound at the exact lower endpoint of the top interval. -/
theorem top_reciprocal_lemma (s γ : ℝ) (hg : γ∈Icc 0 π) :
    (∀ u : ℝ, 0<u → u^2*flux s γ u=(1/u)⁻¹*boundaryFlux (unitDepthSum s γ (1/u))) ∧
    (∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball 0 1) ∧ ∀ v : ℝ, 0<v → v<1 →
      G v=((v⁻¹*boundaryFlux (unitDepthSum s γ v):ℝ):ℂ)) ∧
    (∃ M : ℝ, 0≤M ∧ ∀ u : ℝ, exp (1/2)≤u → |u^2*flux s γ u|≤M) := by
  refine ⟨fun _ hu => reciprocal_flux_scaling s γ hu,reciprocal_flux_analytic s γ hg,?_⟩
  let T := exp (1/2)
  have ht : 1<T := one_lt_exp_iff.mpr (by norm_num)
  obtain ⟨M,hM,hbound⟩ := top_flux_bounded (zero_lt_one.trans ht) (reciprocal_flux_extension s γ hg ht)
  refine ⟨M,hM,fun u hu => ?_⟩
  rw [abs_mul,abs_of_nonneg (sq_nonneg u),mul_comm]
  exact (le_div_iff₀ (sq_pos_of_pos ((zero_lt_one.trans ht).trans_le hu))).mp (hbound u hu)

theorem physical_flux_tail_integrable (s γ : ℝ) (hg : γ∈Icc 0 (π/2)) {u : ℝ} (hu : 0<u) :
    IntegrableOn (flux s γ) (Ioi u) :=
  integrable_flux_tail (T:=2) (by norm_num) hu hg depth_flux_identity
    (flux_continuous_positive s γ hg) (reciprocal_flux_extension s γ ⟨hg.1,by linarith [hg.2,pi_pos]⟩ (by norm_num))

end Liu
