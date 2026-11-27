module

public import Liu.MollifierEstimate
public import Liu.WeakConvolution

@[expose] public section

noncomputable section
open Set Metric MeasureTheory Function Complex Filter
open scoped Topology Convolution ContDiff ENNReal
namespace Liu

/-- Use a normalized smooth bump below the real line so that its reflected
translates are valid interior tests even arbitrarily close to the boundary. -/
theorem weak_analytic_approximation {f : ℂ → ℂ} (hf : Measurable f) (h₂ : MemLp f 2 volume)
    (hw : upperWeakZero f) {ε : ℝ} (he : 0<ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g upper ∧ MemLp g 2 volume ∧ (∫ z, ‖g z-f z‖^2)≤ε^2 := by
  obtain ⟨r,hr,hshift⟩ := small_shift_energy h₂ he
  let c : ℂ := ⟨0,-r/2⟩
  let b : ContDiffBump c := ⟨r/8,r/4,by positivity,by linarith⟩
  let k := b.normed (volume:Measure ℂ)
  let K := fun t => (k t:ℂ)
  have kc : Continuous k := b.continuous_normed
  have k₀ (t : ℂ) : 0≤k t := b.nonneg_normed t
  have mass : ∫ t, k t=1 := b.integral_normed
  have cn : ‖c‖=r/2 := by
    have eq : c=((-r/2:ℝ):ℂ)*I := by apply Complex.ext <;> simp [c]
    rw [eq,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    ring
  have geom (w : ℂ) (hw : w∈closedBall c b.rOut) : w.im≤0 ∧ ‖w‖<r := by
    have hdist : ‖w-c‖≤r/4 := by simpa only [mem_closedBall,dist_eq_norm,b] using hw
    have h₁ := (Complex.im_le_norm (w-c)).trans hdist
    have h₂ := norm_add_le (w-c) c
    rw [sub_add_cancel,cn] at h₂
    rw [Complex.sub_im] at h₁
    change w.im- -r/2≤r/4 at h₁
    constructor <;> linarith
  have hs : tsupport K ⊆ closedBall c b.rOut := by
    rw [←b.tsupport_normed_eq (μ:=volume)]
    exact tsupport_comp_subset (g:=Complex.ofReal) (by simp) k
  have dK : ContDiff ℝ ∞ K := Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  have hcK : HasCompactSupport K := (isCompact_closedBall c b.rOut).of_isClosed_subset (isClosed_tsupport _) hs
  let g := f ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] K
  have dg : DifferentiableOn ℂ g upper := lower_kernel_smoothing (h₂.locallyIntegrable (by norm_num)) hw dK hcK
    (fun w hw => (geom w (hs hw)).1)
  let ν := volume.withDensity (fun t => ENNReal.ofReal (k t))
  have meas : Measurable (fun t => ENNReal.ofReal (k t)) := by fun_prop
  letI : IsProbabilityMeasure ν := ⟨by
    rw [show ν univ=∫⁻ t, ENNReal.ofReal (k t) by simp [ν,withDensity_apply],
      ←ofReal_integral_eq_lintegral_ofReal b.integrable_normed (ae_of_all _ k₀),mass]
    simp⟩
  have hb : ∀ᵐ t ∂ν, (∫ z, ‖f (z-t)-f z‖^2)≤ε^2 := by
    apply (ae_withDensity_iff meas).mpr
    filter_upwards with t ht
    have hk : k t≠0 := fun hh => by simp [hh] at ht
    have hs' : t∈tsupport k := subset_tsupport k hk
    rw [show tsupport k=closedBall c b.rOut from b.tsupport_normed_eq] at hs'
    exact hshift t (geom t hs').2
  have rep (z : ℂ) : (∫ t, f (z-t) ∂ν)=g z := by
    rw [integral_withDensity_eq_integral_toReal_smul meas (ae_of_all _ fun t => ENNReal.ofReal_lt_top) _]
    simp_rw [ENNReal.toReal_ofReal (k₀ _),Complex.real_smul]
    rw [show g z=(∫ t, f (z-t)*K t) from convolution_eq_swap (ContinuousLinearMap.mul ℝ ℂ)]
    apply integral_congr_ae; filter_upwards with t; exact mul_comm _ _
  have H := average_translates_square hf h₂ hb
  dsimp only at H
  simp_rw [rep] at H
  have cg : Continuous g := continuous_iff_continuousAt.mpr fun z => (hcK.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    (h₂.locallyIntegrable (by norm_num)) (dK.of_le (by simp)) z).continuousAt
  have hm : MemLp (g-f) 2 volume :=
    (memLp_two_iff_integrable_sq_norm (cg.aestronglyMeasurable.sub hf.aestronglyMeasurable)).mpr H.1
  exact ⟨g,dg,by simpa only [sub_add_cancel] using hm.add h₂,H.2⟩

end Liu
