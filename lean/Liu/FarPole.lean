import Liu.PowerWindow

noncomputable section
namespace Liu

theorem pole_far_identity {z w : ℂ} (a : ℝ) (h : z≠w) :
    z*pole a w z + (a:ℂ) = w*pole a w z := by
  unfold pole
  field_simp [sub_ne_zero.mpr h]
  ring

def PickSum.farBound {n : ℕ} (p : PickSum n) : ℝ :=
  ∑ i, ‖p.location i‖ * poleBound (p.weight i) (p.location i)

theorem PickSum.far_remainder {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0≤z.im) :
    ‖z*p.value z + (p.mass:ℂ)‖ ≤ p.farBound/(1+‖z‖) := by
  have sep (i : Fin n) : z ≠ p.location i := fun h => by
    have hh := congrArg Complex.im h
    linarith [p.below i]
  have id : z*p.value z+(p.mass:ℂ) =
      ∑ i, p.location i*pole (p.weight i) (p.location i) z := by
    simp only [PickSum.value,PickSum.mass,Complex.ofReal_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact pole_far_identity _ (sep i)
  rw [id,PickSum.farBound,Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro i _
  rw [norm_mul,mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (pole_global_decay (p.pos i) (p.below i) hz) (norm_nonneg _)

end Liu
