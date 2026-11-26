import Mathlib

/-! Integration of a logarithmic majorant above any positive lower depth. -/
open Set MeasureTheory
namespace Liu

theorem log_majorant_integral {f : ℝ → ℝ} {u v A B : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : IntervalIntegrable (fun t => |f t|) volume u v)
    (hp : ∀ t ∈ Icc u v, |f t| ≤ A * Real.log (1/t) + B) :
    (∫ t in u..v, |f t|) ≤ v * (A * (1 + Real.log (1/v)) + B) := by
  let g := fun t : ℝ => A * Real.log (1/t) + B
  let G := fun t : ℝ => t * (A * (1 - Real.log t) + B)
  have pos : ∀ t ∈ uIcc u v, 0 < t := by
    rw [uIcc_of_le huv]
    exact fun t ht => hu.trans_le ht.1
  have cg : ContinuousOn g (uIcc u v) := by
    intro t ht
    dsimp [g]
    have htpos := pos t ht
    fun_prop (disch := first | exact htpos.ne' | exact (one_div_pos.mpr htpos).ne' | positivity)
  have ig := cg.intervalIntegrable (μ := volume)
  have hd : ∀ t ∈ uIcc u v, HasDerivAt G (g t) t := by
    intro t ht
    have h := (pos t ht).ne'
    have d := (hasDerivAt_id t).mul
      (((hasDerivAt_const t A).mul ((hasDerivAt_const t (1:ℝ)).sub (Real.hasDerivAt_log h))).add
        (hasDerivAt_const t B))
    change HasDerivAt (fun x : ℝ => x * (A * (1 - Real.log x) + B)) (A * Real.log (1/t) + B) t
    convert d using 1
    · rfl
    · simp [Pi.add_apply,Pi.mul_apply,Pi.sub_apply,one_div,Real.log_inv,id_eq]
      field_simp [h]
      ring
  have eqn := intervalIntegral.integral_eq_sub_of_hasDerivAt hd ig
  have hG : 0 ≤ G u := by
    have hlog := Real.log_nonpos hu.le (huv.trans hv)
    dsimp [G]
    exact mul_nonneg hu.le (add_nonneg (mul_nonneg hA (by linarith)) hB)
  calc
    (∫ t in u..v, |f t|) ≤ ∫ t in u..v, g t := intervalIntegral.integral_mono_on huv hf ig hp
    _ = G v - G u := eqn
    _ ≤ G v := sub_le_self _ hG
    _ = _ := by simp [G,one_div,Real.log_inv,sub_eq_add_neg]

end Liu
