module

public import Liu.CayleyMonomials

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter Finset
open scoped Topology ComplexConjugate InnerProductSpace
namespace Liu

private theorem l2_pair_integrable {f g : ℂ → ℂ} (hf : MemLp f 2 upperArea) (hg : MemLp g 2 upperArea) :
    Integrable (fun z => f z*conj (g z)) upperArea := by
  have hc : MemLp (fun z => conj (g z)) 2 upperArea := hg.congr_norm
    (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable) (ae_of_all _ fun z => (Complex.norm_conj _).symm)
  exact hf.integrable_mul hc

/-- The Cayley monomials determine every analytic L² vector. -/
theorem upperUnitMonomial_total {x : PlaneL2} (hx : x∈analyticSubspace)
    (hm : ∀ n, inner ℂ (upperUnitMonomial n) x=0) : x=0 := by
  rw [bergman_projection_range] at hx
  obtain ⟨f,hf,hd,rfl⟩ := hx
  have hint (n : ℕ) := l2_pair_integrable hf (upperMonomial_memLp n)
  have hmom (n : ℕ) : (∫ w, f w*conj (upperMonomial n w) ∂upperArea)=0 := by
    have h := hm n
    simp only [upperUnitMonomial,inner_smul_left,Complex.conj_ofReal,upperMonomial_inner,mul_eq_zero] at h
    have hz := h.resolve_left (Complex.ofReal_ne_zero.mpr (sqrt_pos_of_pos (by positivity : 0<(n:ℝ)+1)).ne')
    rw [cayley_pairing]
    exact (setIntegral_congr_fun (s:=disc) Metric.isOpen_ball.measurableSet
      (g:=fun w => cayleyPull Complex.I f w*conj (w^n)) (fun w hw => by dsimp only; rw [cayleyPull_upperMonomial n hw])).trans hz
  have hp (m : ℕ) : (∫ w, f w*conj (uniquenessProbe m w) ∂upperArea)=0 := by
    have he : (fun w => f w*conj (upperMonomial m w)-f w*conj (upperMonomial (m+1) w)) =ᵐ[upperArea]
        (fun w => (-4:ℂ)*(f w*conj (uniquenessProbe m w))) := by
      filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
      have hn : w+Complex.I≠0 := fun h => by
        have hh := congrArg Complex.im h; simp at hh; linarith [show 0<w.im from hw]
      have hid : upperMonomial m w-upperMonomial (m+1) w = (-4:ℂ)*uniquenessProbe m w := by
        dsimp only [upperMonomial,cayleyInv,bergmanKernel,uniquenessProbe]
        rw [Complex.conj_I,sub_neg_eq_add,pow_succ (a:=(w-Complex.I)/(w+Complex.I))]
        simp only [div_pow,pow_add,pow_one]
        field_simp [hn]; ring_nf <;> simp [Complex.I_sq] <;> ring
      rw [←mul_sub,←map_sub,hid,map_mul,map_neg,map_ofNat]; ring
    have H := integral_congr_ae he
    rw [integral_sub (hint m) (hint (m+1)),hmom,hmom,sub_zero,integral_const_mul] at H
    exact (mul_eq_zero.mp H.symm).resolve_left (by norm_num)
  have hzero := uniqueness_of_probe_moments hd (l2_pair_integrable hf (bergmanKernel_memLp (show Complex.I∈upper by simp [upper]))) hp
  apply Lp.ext
  filter_upwards [hf.coeFn_toLp,Lp.coeFn_zero ℂ 2 upperArea,ae_restrict_mem (μ:=area) upper_open.measurableSet] with z ha hb hu
  rw [ha,hb]; exact hzero z hu

/-- Parseval for the actual upper-half-plane Bergman projection, expressed using
the normalized Cayley monomials. -/
theorem project_norm_sq_series (x : PlaneL2) :
    HasSum (fun n => ‖inner ℂ (upperUnitMonomial n) x‖^2) (‖project x‖^2) := by
  letI : analyticSubspace.HasOrthogonalProjection := by unfold analyticSubspace; infer_instance
  let u := upperUnitMonomial
  let c := fun n => inner ℂ (u n) x
  have horth : Orthonormal ℂ u := upperUnitMonomial_orthonormal
  have hc : Summable (fun n => ‖c n‖^2) := horth.inner_products_summable x
  have hv : Summable (fun n => c n • u n) :=
    (horth.orthogonalFamily.summable_iff_norm_sq_summable c).mpr hc
  let y := ∑' n, c n • u n
  have ht : Tendsto (fun N : ℕ => ∑ n ∈ range N, c n • u n) atTop (𝓝 y) := hv.hasSum.tendsto_sum_nat
  have hclosed : IsClosed (analyticSubspace : Set PlaneL2) := by unfold analyticSubspace; exact Submodule.isClosed_topologicalClosure _
  have hy : y∈analyticSubspace := hclosed.mem_of_tendsto ht (Eventually.of_forall fun N =>
    analyticSubspace.sum_mem (fun n _ => analyticSubspace.smul_mem _ (upperUnitMonomial_analytic_mem n)))
  have hPy : project x=y := by
    apply sub_eq_zero.mp
    apply upperUnitMonomial_total (analyticSubspace.sub_mem (analyticSubspace.starProjection_apply_mem x) hy)
    intro n
    have hp := analyticSubspace.inner_starProjection_left_eq_right (u n) x
    change inner ℂ (project (u n)) x=inner ℂ (u n) (project x) at hp
    have hu : project (u n)=u n := Submodule.starProjection_eq_self_iff.mpr (upperUnitMonomial_analytic_mem n)
    rw [hu] at hp
    have hmom := (innerSL ℂ (u n)).continuous.continuousAt.tendsto.comp ht
    have hm : Tendsto (fun N : ℕ => inner ℂ (u n) (∑ i ∈ range N, c i • u i)) atTop (𝓝 (c n)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop n] with N hN using (horth.inner_right_sum c (mem_range.mpr hN)).symm
    change inner ℂ (u n) (project x-y)=0
    rw [inner_sub_right,←hp,show inner ℂ (u n) y=c n from tendsto_nhds_unique hmom hm,sub_self]
  have he : Tendsto (fun N : ℕ => ∑ n ∈ range N, ‖c n‖^2) atTop (𝓝 (‖y‖^2)) := by
    apply (ht.norm.pow 2).congr'
    filter_upwards with N
    exact horth.orthogonalFamily.norm_sum c (range N)
  rw [hPy,←tendsto_nhds_unique hc.hasSum.tendsto_sum_nat he]; exact hc.hasSum

end Liu
