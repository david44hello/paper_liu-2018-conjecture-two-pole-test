module

public import Liu.EdgeTraceL1
public import Liu.PoleArea

@[expose] public section

noncomputable section
open Set Real MeasureTheory
namespace Liu

/-- Real and imaginary traces at the actual edge are defined by the same
operator as at positive depth. -/
def edgeRealTrace (s γ u x : ℝ) : ℝ :=
  depthPoissonReal u x (fun z => (crossSource (normalMass s) (direction γ) z).re)

def edgeImagTrace (s γ u x : ℝ) : ℝ :=
  depthPoissonReal u x (fun z => (crossSource (normalMass s) (direction γ) z).im)

theorem edge_components_at_positive_depth {s γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0<u) (x : ℝ) :
    (edgeCrossTrace s γ u x).re = edgeRealTrace s γ u x ∧
    (edgeCrossTrace s γ u x).im = edgeImagTrace s γ u x := edge_trace_components hg hu x

private theorem source_area_bound {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : 0≤M)
    (hbd : ∀ z : ℂ, 0<z.im → |f z|≤M)
    (hfar : ∀ z : ℂ, 0<z.im → 2≤‖z‖ → |f z|≤4/‖z‖^4) :
    Integrable f upperArea ∧ (∫ z, ‖f z‖ ∂upperArea)≤2*M+1/2 := by
  obtain ⟨hD,hDval⟩ := radialDisc_majorant (w:=0) (by simp) (R:=2) (by norm_num)
  simp only [sub_zero] at hD hDval
  obtain ⟨hT,hTval⟩ := exteriorFourth_integral (T:=2) (by norm_num)
  let G := fun z : ℂ => M*radialDisc 2 ‖z‖+4*exteriorFourth 2 z
  have hi : Integrable G upperArea := (hD.const_mul M).add (hT.const_mul 4)
  have hle : ∀ᵐ z ∂upperArea, ‖f z‖≤G z := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    by_cases h : ‖z‖≤2
    · simpa [G,radialDisc,exteriorFourth,h,not_lt.mpr h,Real.norm_eq_abs] using hbd z hz
    · simpa [G,radialDisc,exteriorFourth,h,lt_of_not_ge h,Real.norm_eq_abs,div_eq_mul_inv] using hfar z hz (le_of_not_ge h)
  have hfi := hi.mono' hf.aestronglyMeasurable hle
  refine ⟨hfi,(integral_mono_ae hfi.norm hi hle).trans ?_⟩
  unfold G
  rw [integral_add (hD.const_mul M) (hT.const_mul 4),integral_const_mul,integral_const_mul,hTval]
  nlinarith only [mul_le_mul_of_nonneg_left hDval hM]

private theorem real_trace_estimates {u M : ℝ} (hu : 0≤u) (hM : 0≤M)
    {f : ℂ → ℝ} (hf : Measurable f)
    (hbd : ∀ z : ℂ, 0<z.im → |f z|≤M)
    (hfar : ∀ z : ℂ, 0<z.im → 2≤‖z‖ → |f z|≤4/‖z‖^4) :
    let c := fun x => depthPoissonReal u x f
    Integrable c ∧ (∫ x, |c x|)/π≤2*M+1/2 ∧ ∀ x, |c x|≤2*M+1/2 := by
  obtain ⟨hfi,harea⟩ := source_area_bound hf hM hbd hfar
  have h := depthPoissonReal_lintegral hf hu
  rw [←ofReal_integral_norm_eq_lintegral_enorm hfi] at h
  have hfin : Integrable (fun x => depthPoissonReal u x f) := by
    refine ⟨(measurable_depthPoissonReal hf u).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_enorm,lt_top_iff_ne_top]
    intro he
    rw [he,ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h)
  rw [←ofReal_integral_norm_eq_lintegral_enorm hfin,←ENNReal.ofReal_mul (by positivity)] at h
  have hreal := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => norm_nonneg _))).mp h
  dsimp only
  refine ⟨hfin,?_,depthPoissonReal_uniform hu hM f hbd hfar⟩
  simpa only [Real.norm_eq_abs,div_eq_mul_inv,one_mul,mul_comm π⁻¹] using hreal.trans harea

/-- L¹ and pointwise (hence L∞) parts of E.3(a), with the paper's line
normalization. The bounds continue to hold at zero. -/
theorem edge_real_trace_separated {s γ u : ℝ} (hg : γ∈Icc 0 (π/2))
    (hc : 1/2≤cos γ) (hu : 0≤u) :
    let μ := min (normalMass s) (1-normalMass s)
    let C₁ := 2^15/μ
    Integrable (edgeRealTrace s γ u) ∧ (∫ x, |edgeRealTrace s γ u x|)/π≤C₁ ∧
      ∀ x, |edgeRealTrace s γ u x|≤5*C₁ := by
  let μ := min (normalMass s) (1-normalMass s)
  have hμ : 0<μ := lt_min (Certificate.normalMass_pos _) (by
    rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _)
  have hμ₁ : μ≤1 := (min_le_right ..).trans (by linarith [Certificate.normalMass_pos s])
  have hfar (z : ℂ) (hz : 0<z.im) (hr : 2≤‖z‖) :=
    (Complex.abs_re_le_norm _).trans ((edge_source_separated_feet (s:=s) hg hc hz).2.2.2 hr)
  obtain ⟨hi,h₁,hsup⟩ := real_trace_estimates (M:=2048/μ) hu (by positivity)
    (Complex.measurable_re.comp (measurable_crossSource (normalMass s) (direction γ)))
    (fun _ hz => edge_real_source_uniform hg hc hz) hfar
  have hcmp : 2*(2048/μ)+1/2≤2^15/μ := by
    field_simp [hμ.ne']; nlinarith
  exact ⟨hi,h₁.trans hcmp,fun x => (hsup x).trans (hcmp.trans (by change 2^15/μ≤5*(2^15/μ); linarith [show 0≤(2:ℝ)^15/μ by positivity]))⟩

/-- The real trace estimates in E.3(b) at every nonnegative depth. -/
theorem edge_real_trace_fixed {s γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hσ : 0<sin γ) (hu : 0≤u) :
    let C₂ := 8/(normalMass s*sin γ^4)
    Integrable (edgeRealTrace s γ u) ∧ (∫ x, |edgeRealTrace s γ u x|)/π≤C₂ ∧
      ∀ x, |edgeRealTrace s γ u x|≤3*C₂ := by
  let a := normalMass s
  let b := 1-a
  have ha : 0<a := Certificate.normalMass_pos _
  have hb : 0<b := by dsimp [a,b]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _
  have ha₁ : a≤1 := by dsimp only [b] at hb; linarith
  have hb₁ : b≤1 := by dsimp only [b]; linarith
  have hd : 0<a*sin γ^4 := by positivity
  have hd₁ : a*sin γ^4≤1 := by
    have hh := pow_le_pow_left₀ hσ.le (sin_le_one γ) 4
    norm_num at hh
    nlinarith only [mul_le_mul_of_nonneg_left hh ha.le,ha₁]
  have hfar (z : ℂ) (hz : 0<z.im) (hr : 2≤‖z‖) :=
    (Complex.abs_re_le_norm _).trans ((edge_source_fixed_angle (s:=s) hg hσ hz).2.2 hr)
  obtain ⟨hi,h₁,hsup⟩ := real_trace_estimates (M:=2*b/(a*sin γ^4)) hu (by positivity)
    (Complex.measurable_re.comp (measurable_crossSource (normalMass s) (direction γ)))
    (fun _ hz => (edge_source_fixed_angle (s:=s) hg hσ hz).1) hfar
  have hcmp : 2*(2*b/(a*sin γ^4))+1/2≤8/(a*sin γ^4) := by
    apply (le_div_iff₀ hd).mpr
    field_simp [hd.ne']; nlinarith
  exact ⟨hi,h₁.trans hcmp,fun x => (hsup x).trans (hcmp.trans (by change 8/(a*sin γ^4)≤3*(8/(a*sin γ^4)); linarith [show 0≤8/(a*sin γ^4) by positivity]))⟩

end Liu
