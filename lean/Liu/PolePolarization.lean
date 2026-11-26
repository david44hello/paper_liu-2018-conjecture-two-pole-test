import Liu.SeparatedDomain
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace Liu

/-- At i this affine family attains p and its reflected partner attains conj c.
On the real axis the two are genuine complex conjugates. -/
def polarPole (p c w : ℂ) : ℂ := (p+c)/2 + w*((p-c)/(2*Complex.I))

def polarWindow (p c : ℂ) : Set ℂ :=
  {w | (polarPole p c w).im<0 ∧ (polarPole p c (conj w)).im<0}

theorem polar_points {p c : ℂ} (hp : p.im<0) (hc : c.im<0) :
    polarPole p c Complex.I=p ∧ polarPole p c (-Complex.I)=c ∧
    (0:ℂ)∈polarWindow p c ∧ Complex.I∈polarWindow p c := by
  have hi : polarPole p c Complex.I=p := by unfold polarPole; field_simp [Complex.I_ne_zero]; ring
  have hn : polarPole p c (-Complex.I)=c := by unfold polarPole; field_simp [Complex.I_ne_zero]; ring
  have h₀ : (polarPole p c 0).im<0 := by simp [polarPole,Complex.div_ofNat_im]; linarith
  exact ⟨hi,hn,⟨h₀,by simpa only [map_zero] using h₀⟩,⟨by simpa only [hi] using hp,by simpa only [Complex.conj_I,hn] using hc⟩⟩

theorem polar_window_open (p c : ℂ) : IsOpen (polarWindow p c) := by
  have hl : Continuous (fun w => (polarPole p c w).im) := by unfold polarPole; fun_prop
  have hr : Continuous (fun w => (polarPole p c (conj w)).im) := hl.comp (by fun_prop)
  exact (isOpen_lt hl continuous_const).inter (isOpen_lt hr continuous_const)

theorem polar_window_convex (p c : ℂ) : Convex ℝ (polarWindow p c) := by
  have aff (a b : ℝ) (hab : a+b=1) (x y : ℂ) :
      polarPole p c (a • x+b • y)=a • polarPole p c x+b • polarPole p c y := by
    have eh := congrArg Complex.ofReal hab
    push_cast at eh
    simp only [polarPole,Complex.real_smul]
    linear_combination -(p+c)/2 * eh
  intro x hx y hy a b ha hb hab
  have neg (X Y : ℂ) (hX : X.im<0) (hY : Y.im<0) : (a • X + b • Y).im<0 := by
    simp only [Complex.add_im,Complex.real_smul,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    rcases ha.eq_or_lt with he|ha'
    · subst a; simp_all
    · linarith [mul_neg_of_pos_of_neg ha' hX,mul_nonpos_of_nonneg_of_nonpos hb hY.le]
  constructor
  · rw [aff a b hab]; exact neg _ _ hx.1 hy.1
  · have e : conj (a • x+b • y)=a • conj x+b • conj y := by simp [Complex.real_smul]
    rw [e,aff a b hab]; exact neg _ _ hx.2 hy.2

theorem polar_identity {p c : ℂ} (hp : p.im<0) (hc : c.im<0) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (polarWindow p c)) (hg : AnalyticOnNhd ℂ g (polarWindow p c))
    (he : ∀ r : ℝ, (r:ℂ)∈polarWindow p c → f r=g r) : f Complex.I = g Complex.I := by
  obtain ⟨_,_,h₀,hi⟩ := polar_points hp hc
  apply hf.eqOn_of_preconnected_of_frequently_eq hg (polar_window_convex p c).isPreconnected h₀ _ hi
  have hreal : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[>] 0) (𝓝[≠] (0:ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0<t)
    exact Complex.ofReal_ne_zero.mpr ht.ne'
  apply hreal.frequently
  have hn : ∀ᶠ r : ℝ in 𝓝 0, (r:ℂ)∈polarWindow p c :=
    Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (by simpa using (polar_window_open p c).mem_nhds h₀)
  exact ((hn.mono fun r hr => he r hr).filter_mono nhdsWithin_le_nhds).frequently

end Liu
