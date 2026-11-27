module

public import Liu.SingleFlux

@[expose] public section

noncomputable section
open Set MeasureTheory Real
namespace Liu

theorem isolatedTrace_memLp (a : ℝ) {b : ℝ} (hb : 0 < b) :
    MemLp (isolatedTrace a b) 2 volume := by
  have hm : Measurable (fun p : ℝ × ℝ => poissonLine a p.2 p.1/(p.2+b)) := by unfold poissonLine; fun_prop
  have hs : StronglyMeasurable (isolatedTrace a b) := hm.stronglyMeasurable.integral_prod_right' (ν:=volume.restrict (Ioi b))
  apply (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mpr
  have h := (div_eq_iff pi_ne_zero).mp (isolatedTrace_energy a hb)
  apply Integrable.of_integral_ne_zero
  rw [h,k₀]; positivity

theorem PickSum.field_memLp_boundary {n : ℕ} (p : PickSum n) :
    MemLp (fun x : ℝ => field p.value x) 2 volume := by
  let g := fun (i : Fin n) (x : ℝ) => p.weight i*isolatedTrace (p.location i).re (-(p.location i).im) x
  have hi (i : Fin n) : MemLp (g i) 2 volume :=
    (isolatedTrace_memLp _ (neg_pos.mpr (p.below i))).const_mul _
  have hsum := memLp_finsetSum Finset.univ (fun i _ => hi i)
  have hf : Measurable (field p.value) := by unfold field; fun_prop
  apply hsum.mono ((hf.comp Complex.measurable_ofReal).aestronglyMeasurable)
  filter_upwards with x
  have hnn : 0 ≤ ∑ i, g i x := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (p.pos i).le (isolatedTrace_nonneg _ _ (neg_pos.mpr (p.below i))))
  simpa [Real.norm_eq_abs,abs_of_nonneg hnn,g] using p.field_bounded_by_isolated x

end Liu
