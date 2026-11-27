module

public import Liu.Pick

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace Liu

/-- Reflected Dirichlet kernel in the normalization used by the source potential. -/
def greenLog (z w : ℂ) : ℝ := Real.log (‖z-conj w‖ / ‖z-w‖)

def greenAtHeight (x X Y y : ℝ) : ℝ :=
  (Real.log ((x-X)^2 + (y+Y)^2) - Real.log ((x-X)^2 + (y-Y)^2))/2

theorem greenLog_formula (z w : ℂ) (h₁ : z ≠ conj w) (h₂ : z ≠ w) :
    greenLog z w = greenAtHeight z.re w.re w.im z.im := by
  have hA : 0 < ‖z-conj w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h₁)
  have hB : 0 < ‖z-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h₂)
  have sq₁ : ‖z-conj w‖^2 = (z.re-w.re)^2 + (z.im+w.im)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [pow_two]
  have sq₂ : ‖z-w‖^2 = (z.re-w.re)^2 + (z.im-w.im)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [pow_two]
  unfold greenLog greenAtHeight
  rw [Real.log_div hA.ne' hB.ne',←sq₁,←sq₂,Real.log_pow,Real.log_pow]
  ring

theorem greenLog_boundary_derivative (x X Y : ℝ) (hY : 0 < Y) :
    HasDerivAt (greenAtHeight x X Y) (2*Y / ((x-X)^2+Y^2)) 0 := by
  have hp : 0 < (x-X)^2+Y^2 := by positivity
  have plus := (((hasDerivAt_id (0:ℝ)).add_const Y).pow 2).const_add ((x-X)^2)
  have minus := (((hasDerivAt_id (0:ℝ)).sub_const Y).pow 2).const_add ((x-X)^2)
  have d := ((plus.log (by simpa using hp.ne')).sub (minus.log (by simpa using hp.ne'))).div_const 2
  convert d using 1 <;> first | rfl | (simp; field_simp; ring)

end Liu
