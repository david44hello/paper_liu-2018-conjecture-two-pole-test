import Liu.MainImplications

noncomputable section
open scoped ComplexConjugate
open Set
namespace Liu

def reflectIf (flip : Bool) (z : ℂ) : ℂ := if flip then -conj z else z

theorem reflectIf_im (f : Bool) (z : ℂ) : (reflectIf f z).im = z.im := by cases f <;> simp [reflectIf]
theorem reflectIf_sub (f : Bool) (z w : ℂ) : reflectIf f (z-w) = reflectIf f z - reflectIf f w := by
  cases f <;> simp [reflectIf] <;> ring
theorem reflectIf_norm (f : Bool) (z : ℂ) : ‖reflectIf f z‖ = ‖z‖ := by cases f <;> simp [reflectIf]

/-- A rightward, downward unit displacement has exactly the angular form used by the certificate. -/
theorem direction_of_quadrant {v : ℂ} (hn : ‖v‖=1) (hx : 0≤v.re) (hy : v.im≤0) :
    ∃ γ ∈ Icc 0 (Real.pi/2), direction γ = v := by
  let γ := (conj v).arg
  have hp : 0 ≤ γ := Complex.arg_nonneg_iff.mpr (by simpa)
  have hb : γ ≤ Real.pi/2 := Complex.arg_le_pi_div_two_iff.mpr (Or.inl (by simpa))
  have h := Complex.norm_mul_exp_arg_mul_I (conj v)
  rw [Complex.norm_conj,hn,Complex.ofReal_one,one_mul] at h
  have h' := congrArg (fun w : ℂ => conj w) h
  refine ⟨γ,⟨hp,hb⟩,?_⟩
  simpa [direction,γ,← Complex.exp_conj] using h'

def transformedPole (f : Bool) (x d : ℝ) (w : ℂ) : ℂ :=
  reflectIf f (w-(x:ℂ)) / (d:ℂ)

/-- Normalize an ordered pair of distinct poles. The orientation test permits equal depths
and vertical displacements. Translation, reflection and dilation are exhibited explicitly. -/
theorem normalize_ordered {w₁ w₂ : ℂ} (hbelow : w₁.im < 0)
    (horder : w₂.im ≤ w₁.im) (hdiff : w₂ ≠ w₁) :
    let d := ‖w₂-w₁‖
    ∃ f : Bool, ∃ γ ∈ Icc 0 (Real.pi/2), ∃ u : ℝ, 0 < u ∧
      transformedPole f w₁.re d w₁ = -(u:ℂ)*Complex.I ∧
      transformedPole f w₁.re d w₂ = -(u:ℂ)*Complex.I + direction γ := by
  let Δ := w₂-w₁
  let d := ‖Δ‖
  let f := decide (Δ.re < 0)
  let v := reflectIf f Δ / (d:ℂ)
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hdiff)
  have hn : ‖v‖=1 := by simp [v,norm_div,reflectIf_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd,d,hd.ne']
  have hr : 0 ≤ v.re := by
    change 0 ≤ (reflectIf f Δ / (d:ℂ)).re
    rw [Complex.div_ofReal_re]
    apply div_nonneg _ hd.le
    unfold reflectIf f
    split <;> simp_all <;> linarith
  have hi : v.im ≤ 0 := by
    change (reflectIf f Δ / (d:ℂ)).im ≤ 0
    rw [Complex.div_ofReal_im,reflectIf_im]
    exact div_nonpos_of_nonpos_of_nonneg (by simp [Δ,horder]) hd.le
  obtain ⟨γ,hγ,hv⟩ := direction_of_quadrant hn hr hi
  let u := -w₁.im/d
  have hu : 0<u := div_pos (neg_pos.mpr hbelow) hd
  have hw₁ : transformedPole f w₁.re d w₁ = -(u:ℂ)*Complex.I := by
    cases h : f <;> apply Complex.ext <;> simp [transformedPole,reflectIf,Complex.mul_re,Complex.mul_im,u] <;> ring
  refine ⟨f,γ,hγ,u,hu,hw₁,?_⟩
  rw [←hw₁,hv]
  dsimp [transformedPole,v]
  rw [←add_div]
  congr 1
  cases f <;> simp [reflectIf,Δ] <;> ring

theorem normalized_weights {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    normalMass (Real.log (b/a)) = a/(a+b) ∧
    1-normalMass (Real.log (b/a)) = b/(a+b) := by
  simp only [normalMass,Real.exp_log (div_pos hb ha)]
  constructor <;> field_simp <;> ring

end Liu
