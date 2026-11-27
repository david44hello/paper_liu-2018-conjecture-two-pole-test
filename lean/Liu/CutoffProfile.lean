module

public import Liu.AngularControl
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section

noncomputable section
open Set Real Filter
open scoped Topology
namespace Liu

/-- The cutoff in log-radius is zero up to radius one and one from radius two. -/
def radialCutoff (s : ℝ) : ℝ := Real.smoothTransition (s/log 2)

private theorem radialCutoff_smooth (n : ℕ) : ContDiff ℝ n radialCutoff := by
  exact Real.smoothTransition.contDiff.comp (contDiff_id.div_const _)

private theorem cutoff_derivs :
    Differentiable ℝ radialCutoff ∧ Differentiable ℝ (deriv radialCutoff) ∧ Differentiable ℝ (deriv (deriv radialCutoff)) := by
  exact ⟨(radialCutoff_smooth 1).differentiable one_ne_zero,
    (show ContDiff ℝ 1 (deriv radialCutoff) from (radialCutoff_smooth 2).deriv').differentiable one_ne_zero,
    (show ContDiff ℝ 1 (deriv (deriv radialCutoff)) from ((radialCutoff_smooth 3).deriv' (n:=2)).deriv').differentiable one_ne_zero⟩

def modelRadial (t s : ℝ) : ℂ := ((radialCutoff s*exp (-t*s):ℝ):ℂ)
def modelRadialD (t s : ℝ) : ℂ := (((deriv radialCutoff s-t*radialCutoff s)*exp (-t*s):ℝ):ℂ)
def modelRadialDD (t s : ℝ) : ℂ := (((deriv (deriv radialCutoff) s-2*t*deriv radialCutoff s+t^2*radialCutoff s)*exp (-t*s):ℝ):ℂ)

theorem modelRadial_derivatives (t s : ℝ) :
    HasDerivAt (modelRadial t) (modelRadialD t s) s ∧ HasDerivAt (modelRadialD t) (modelRadialDD t s) s ∧
    DifferentiableAt ℝ (modelRadialDD t) s := by
  obtain ⟨hc,hd,he⟩ := cutoff_derivs
  have de := (((hasDerivAt_id s).const_mul (-t)).exp)
  have dc := (hc s).hasDerivAt
  have dd := (hd s).hasDerivAt
  constructor
  · convert (dc.mul de).ofReal_comp using 1
    · rfl
    · simp [modelRadial,modelRadialD,id_eq] <;> push_cast <;> ring
  constructor
  · convert ((dd.sub (dc.const_mul t)).mul de).ofReal_comp using 1
    · rfl
    · simp [modelRadialD,modelRadialDD,id_eq] <;> push_cast <;> ring
  · exact Complex.ofRealCLM.differentiableAt.comp s (((he s).sub ((hd s).const_mul (2*t)) |>.add ((hc s).const_mul (t^2))).mul de.differentiableAt)

private theorem cutoff_plateau {s c : ℝ} (h : radialCutoff =ᶠ[𝓝 s] (fun _ => c)) :
    radialCutoff s=c ∧ deriv radialCutoff s=0 ∧ deriv (deriv radialCutoff) s=0 := by
  have he := h.deriv
  have hf := he.deriv
  exact ⟨h.eq_of_nhds,by simpa using he.eq_of_nhds,by simpa using hf.eq_of_nhds⟩

theorem modelRadial_near_zero (t : ℝ) {s : ℝ} (hs : s<0) :
    modelRadial t s=0 ∧ modelRadialD t s=0 ∧ modelRadialDD t s=0 := by
  have h : radialCutoff =ᶠ[𝓝 s] (fun _ => 0) := by
    filter_upwards [gt_mem_nhds hs] with u hu
    exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hu.le (log_nonneg (by norm_num)))
  obtain ⟨h0,h1,h2⟩ := cutoff_plateau h
  simp [modelRadial,modelRadialD,modelRadialDD,h0,h1,h2]

theorem modelRadial_far (t : ℝ) {s : ℝ} (hs : log 2<s) :
    modelRadial t s=(exp (-t*s):ℂ) ∧ modelRadialD t s= -(t:ℂ)*modelRadial t s ∧
      modelRadialDD t s=(t:ℂ)^2*modelRadial t s := by
  have h : radialCutoff =ᶠ[𝓝 s] (fun _ => 1) := by
    filter_upwards [lt_mem_nhds hs] with u hu
    exact Real.smoothTransition.one_of_one_le ((one_le_div (log_pos (by norm_num))).mpr hu.le)
  obtain ⟨h0,h1,h2⟩ := cutoff_plateau h
  simp [modelRadial,modelRadialD,modelRadialDD,h0,h1,h2]

theorem modelRadial_uniform {T : ℝ} (hT : 0≤T) :
    ∃ M ≥ 0, ∀ t∈Icc (0:ℝ) 1, ∀ s ≤ T, ‖modelRadial t s‖≤M ∧ ‖modelRadialD t s‖≤M ∧ ‖modelRadialDD t s‖≤M := by
  obtain ⟨hc,hd,he⟩ := cutoff_derivs
  let K := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) T
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have cc : Continuous radialCutoff := hc.continuous
  have cd : Continuous (deriv radialCutoff) := hd.continuous
  have ce : Continuous (deriv (deriv radialCutoff)) := he.continuous
  have h₀ : Continuous (fun p : ℝ×ℝ => modelRadial p.1 p.2) := by
    unfold modelRadial; fun_prop (disch := first | exact hc.continuous | assumption)
  have h₁ : Continuous (fun p : ℝ×ℝ => modelRadialD p.1 p.2) := by
    unfold modelRadialD; fun_prop (disch := first | exact hc.continuous | exact hd.continuous | assumption)
  have h₂ : Continuous (fun p : ℝ×ℝ => modelRadialDD p.1 p.2) := by
    unfold modelRadialDD; fun_prop (disch := first | exact hc.continuous | exact hd.continuous | exact he.continuous | assumption)
  obtain ⟨A,ha⟩ := hK.exists_bound_of_continuousOn h₀.continuousOn
  obtain ⟨B,hb⟩ := hK.exists_bound_of_continuousOn h₁.continuousOn
  obtain ⟨C,hc'⟩ := hK.exists_bound_of_continuousOn h₂.continuousOn
  refine ⟨|A|+|B|+|C|,by positivity,?_⟩
  intro t ht s hs
  by_cases hz : 0 ≤ s
  · have hk : (t,s)∈K := ⟨ht,hz,hs⟩
    have h₀ := ha (t,s) hk; have h₁ := hb (t,s) hk; have h₂ := hc' (t,s) hk
    dsimp only at h₀ h₁ h₂
    exact ⟨by linarith [le_abs_self A,abs_nonneg B,abs_nonneg C],by linarith [le_abs_self B,abs_nonneg A,abs_nonneg C],by linarith [le_abs_self C,abs_nonneg A,abs_nonneg B]⟩
  · obtain ⟨h,h',h''⟩ := modelRadial_near_zero t (lt_of_not_ge hz)
    simp [h,h',h'']; positivity

end Liu
