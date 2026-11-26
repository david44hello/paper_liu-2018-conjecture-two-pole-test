import Liu.PoissonLine

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

theorem poissonLine_pair_all (a c : ℝ) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    ∫ x, poissonLine a b x*poissonLine c d x = π*(b+d)/((c-a)^2+(b+d)^2) := by
  by_cases hn : b≠d
  · exact poissonLine_pair a c hb hd hn
  have heq := not_ne_iff.mp hn
  subst d
  have hp : Integrable (poissonLine a b) :=
    Integrable.of_integral_ne_zero ((poissonLine_integral a hb) ▸ pi_ne_zero)
  have hdiv := hp.div_const b
  have ht := (show Tendsto (fun t : ℝ => t) (𝓝[>] b) (𝓝 b) from nhdsWithin_le_nhds)
  have hlim : Tendsto (fun t : ℝ => ∫ x, poissonLine a b x*poissonLine c t x) (𝓝[>] b)
      (𝓝 (∫ x, poissonLine a b x*poissonLine c b x)) := by
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hdiv ?_
    · apply Eventually.of_forall
      intro t
      exact (show Measurable (fun x => poissonLine a b x*poissonLine c t x) by unfold poissonLine; fun_prop).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin (a:=b) (s:=Ioi b)] with t ht
      filter_upwards with x
      have ht0 := hb.trans ht
      have h1 : 0 ≤ poissonLine a b x := by unfold poissonLine; positivity
      have h2 : 0 ≤ poissonLine c t x := by unfold poissonLine; positivity
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg h1 h2),div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ h1
      unfold poissonLine
      rw [←one_div,div_le_div_iff₀ (by positivity) hb]
      nlinarith [sq_nonneg (x-c),mul_nonneg ht0.le (sub_nonneg.mpr ht.le)]
    · filter_upwards with x
      have hc : ContinuousAt (fun t : ℝ => poissonLine a b x*poissonLine c t x) b := by
        unfold poissonLine; fun_prop (disch := positivity)
      exact hc.tendsto.comp ht
  have hC : ContinuousAt (fun t : ℝ => π*(b+t)/((c-a)^2+(b+t)^2)) b := by fun_prop (disch := positivity)
  apply tendsto_nhds_unique hlim
  apply (hC.tendsto.comp ht).congr'
  filter_upwards [self_mem_nhdsWithin (a:=b) (s:=Ioi b)] with t ht
  exact (poissonLine_pair a c hb (hb.trans ht) (ne_of_lt ht)).symm

end Liu
