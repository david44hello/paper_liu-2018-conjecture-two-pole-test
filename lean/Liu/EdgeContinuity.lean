import Liu.EdgeModulusIntegral
import Liu.EdgeRealTrace

noncomputable section
open Set Real MeasureTheory
namespace Liu

private theorem modulus_from_slices {f : ℂ → ℝ} (hf : Measurable f) {C h u v x x' : ℝ}
    (hC : 0≤C) (hh : 0<h) (hh₁ : h≤1/4) (hu : 0≤u) (hv : 0≤v)
    (hbd : ∀ z : ℂ, 0<z.im → |f z|≤C/4)
    (htail : ∀ z : ℂ, 1<z.im → |f z|≤C/z.im^2)
    (hdelta : ∀ Y, 2*h<Y → ∀ M : ℝ, (∀ X, |f ⟨X,Y⟩|≤M) →
      |edgeSlice f u x Y-edgeSlice f v x' Y|≤2*M*h/Y) :
    |depthPoissonReal u x f-depthPoissonReal v x' f|≤4*C*h*(1+log (1/h)) := by
  have hbd' (z : ℂ) (hz : 0<z.im) : |f z|≤C := (hbd z hz).trans (by linarith)
  rw [←edgeSlice_integral,←edgeSlice_integral]
  apply log_modulus_integral hC hh hh₁ (edgeSlice_integrable hf hu hC hbd' htail x)
    (edgeSlice_integrable hf hv hC hbd' htail x')
  · intro Y hY
    simp [edgeSlice,show ¬u<Y by linarith,show ¬v<Y by linarith]
  · intro Y hY
    apply (abs_sub _ _).trans
    have h₁ := edgeSlice_le (u:=u) (x:=x) (show 0≤C/4 by positivity) (fun _ X => hbd ⟨X,Y⟩ hY)
    have h₂ := edgeSlice_le (u:=v) (x:=x') (show 0≤C/4 by positivity) (fun _ X => hbd ⟨X,Y⟩ hY)
    linarith
  · intro Y hY _
    exact hdelta Y hY C (fun X => hbd' ⟨X,Y⟩ (by change 0<Y; linarith))
  · intro Y hY
    have hy : 0<Y := by linarith
    apply (hdelta Y (by linarith) (C/Y^2) (fun X => htail ⟨X,Y⟩ hY)).trans
    apply (div_le_iff₀ hy).mpr
    have hn : 0≤2*C*h/Y^2 := by positivity
    calc
      2*(C/Y^2)*h = 2*C*h/Y^2 := by ring
      _ ≤ (2*C*h/Y^2)*Y := le_mul_of_one_le_right hn hY.le

private theorem fixed_real_envelope {s γ : ℝ} (hg : γ∈Icc 0 (π/2)) (hσ : 0<sin γ) :
    let f := fun z => (crossSource (normalMass s) (direction γ) z).re
    let C := 8/(normalMass s*sin γ^4)
    0≤C ∧ (∀ z : ℂ, 0<z.im → |f z|≤C/4) ∧ (∀ z : ℂ, 1<z.im → |f z|≤C/z.im^2) := by
  let a := normalMass s
  let D := a*sin γ^4
  let C := 8/D
  have ha : 0<a := Certificate.normalMass_pos _
  have ha₁ : a≤1 := by dsimp [a]; linarith [Certificate.complement_normalMass s,Certificate.normalMass_pos (-s)]
  have hD : 0<D := by dsimp [D]; positivity
  have hD₁ : D≤1 := by
    have hs := pow_le_pow_left₀ hσ.le (sin_le_one γ) 4
    norm_num at hs; exact (mul_le_mul_of_nonneg_left hs ha.le).trans (by simpa using ha₁)
  have hC : 8≤C := by change 8≤8/D; rw [le_div_iff₀ hD]; linarith
  have Hb (z : ℂ) (hz : 0<z.im) : |(crossSource a (direction γ) z).re|≤C/4 := by
    apply ((edge_source_fixed_angle (s:=s) hg hσ hz).1).trans
    change 2*(1-a)/D≤(8/D)/4
    calc
      _ ≤ 2/D := div_le_div_of_nonneg_right (by linarith) hD.le
      _ = _ := by ring
  refine ⟨by change 0≤C; linarith,Hb,?_⟩
  intro z hY
  have hy : 0<z.im := by linarith
  have hr := hy.trans_le (Complex.im_le_norm z)
  by_cases h : z.im≤2
  · apply (Hb z hy).trans
    apply (le_div_iff₀ (sq_pos_of_pos hy)).mpr
    change C/4*z.im^2≤C
    nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy.le h 2) (show 0≤C from by linarith)]
  · have h₂ : 2≤‖z‖ := (lt_of_not_ge h).le.trans (Complex.im_le_norm z)
    apply ((Complex.abs_re_le_norm _).trans ((edge_source_fixed_angle (s:=s) hg hσ hy).2.2 h₂)).trans
    change 4/‖z‖^4≤C/z.im^2
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hsq := pow_le_pow_left₀ hy.le (Complex.im_le_norm z) 2
    have hr₁ : 1≤‖z‖^2 := by nlinarith [sq_nonneg (‖z‖-2)]
    nlinarith only [hsq,mul_le_mul_of_nonneg_left hr₁ (sq_nonneg ‖z‖),
      mul_le_mul_of_nonneg_right hC (pow_nonneg hr.le 4),pow_nonneg hr.le 4]

/-- The spatial modulus and the uniform-in-x depth modulus in E.3(b). -/
theorem edge_real_trace_moduli {s γ : ℝ} (hg : γ∈Icc 0 (π/2)) (hσ : 0<sin γ) :
    let C := 8/(normalMass s*sin γ^4)
    (∀ x : ℝ, 0 < |x| → |x|≤1/4 →
      |edgeRealTrace s γ 0 x-edgeRealTrace s γ 0 0|≤4*C*|x| *(1+log (1/|x|))) ∧
    (∀ u : ℝ, 0<u → u≤1/4 → ∀ x : ℝ,
      |edgeRealTrace s γ u x-edgeRealTrace s γ 0 x|≤4*C*u*(1+log (1/u))) := by
  let f := fun z => (crossSource (normalMass s) (direction γ) z).re
  have hf : Measurable f := Complex.measurable_re.comp (measurable_crossSource ..)
  have hs (Y : ℝ) : Measurable (fun X : ℝ => f ⟨X,Y⟩) :=
    hf.comp (Complex.measurableEquivRealProd.symm.measurable.comp (measurable_id.prodMk measurable_const))
  obtain ⟨hC,hbd,htail⟩ := fixed_real_envelope (s:=s) hg hσ
  constructor
  · intro x hx hx₁
    apply modulus_from_slices hf hC hx hx₁ le_rfl le_rfl hbd htail
    intro Y hY M hM
    have hy : 0<Y := by linarith
    have hn : 0≤M := (abs_nonneg _).trans (hM 0)
    simp only [edgeSlice,indicator_of_mem (show Y∈Ioi (0:ℝ) from hy),sub_zero]
    apply (edgeAverage_space hy x 0 (hs Y) hM).trans
    rw [sub_zero]
    apply div_le_div_of_nonneg_right _ hy.le
    nlinarith only [mul_nonneg hn hx.le]
  · intro u hu hu₁ x
    apply modulus_from_slices hf hC hu hu₁ hu.le le_rfl hbd htail
    intro Y hY M hM
    have hy : 0<Y := by linarith
    have huy : u<Y := by linarith
    have hn : 0≤M := (abs_nonneg _).trans (hM 0)
    simp only [edgeSlice,indicator_of_mem (show Y∈Ioi (0:ℝ) from hy),indicator_of_mem (show Y∈Ioi u from huy),sub_zero]
    apply (edgeAverage_height (sub_pos.mpr huy) (by linarith : Y-u≤Y) x (hs Y) hM).trans
    apply (div_le_div_iff₀ (sub_pos.mpr huy) hy).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hY.le (mul_nonneg hn hu.le)]

end Liu
