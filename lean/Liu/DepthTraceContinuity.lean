import Liu.EdgeTrace

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped ComplexConjugate Topology
namespace Liu

def depthTranslate (S : ℂ → ℂ) (t : ℝ) (z : ℂ) := S (z+(t:ℂ)*Complex.I)

def PickSum.deeper {n : ℕ} (p : PickSum n) (t : ℝ) (ht : 0≤t) : PickSum n where
  nonempty := p.nonempty
  weight := p.weight
  location := fun i => p.location i-(t:ℂ)*Complex.I
  pos := p.pos
  below := fun i => by simp; linarith [p.below i]

theorem PickSum.deeper_value {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0≤t) :
    (p.deeper t ht).value=depthTranslate p.value t := by
  funext z; dsimp [depthTranslate,PickSum.value,PickSum.deeper,pole]
  apply Finset.sum_congr rfl; intro i _
  rw [show z-(p.location i-(t:ℂ)*Complex.I)=z+(t:ℂ)*Complex.I-p.location i by ring]

theorem source_depthTranslate (S : ℂ → ℂ) (t : ℝ) (z : ℂ) :
    source (depthTranslate S t) z=source S (z+(t:ℂ)*Complex.I) := by
  change source (fun w => S (w+(t:ℂ)*Complex.I)) z=source S (z+(t:ℂ)*Complex.I)
  simp only [source,deriv_comp_add_const]

private theorem depth_distance {w z : ℂ} (hw : w.im<0) (hz : 0≤z.im) {t : ℝ} (ht : 0≤t) :
    ‖z-w‖^2≤‖z+(t:ℂ)*Complex.I-w‖^2 := by
  simp [Complex.sq_norm,Complex.normSq_apply]
  nlinarith only [mul_nonneg ht (show 0≤z.im-w.im by linarith),sq_nonneg t]

theorem PickSum.trace_depth_majorant {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0≤t)
    {z : ℂ} (hz : z∈upper) (x : ℝ) :
    ‖traceDensity (depthTranslate p.value t) x z‖ ≤ ∑ i, isolatedDensity (p.weight i) (p.location i) x z := by
  let v := z+(t:ℂ)*Complex.I
  have hz' : 0<z.im := hz
  have hv : 0≤v.im := by dsimp [v]; simp; linarith
  have hval : p.value v≠0 := fun e => by have hh := p.value_im_pos hv; simp [e] at hh
  have hder := norm_sum_le (Finset.univ : Finset (Fin n)) (fun i => (p.weight i:ℂ)/(v-p.location i)^2)
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,norm_pow] at hder
  simp_rw [abs_of_pos (p.pos _)] at hder
  have hd : ‖deriv p.value v‖ ≤ ∑ i, p.weight i/‖z-p.location i‖^2 := by
    rw [(p.hasDerivAt hv).deriv]
    apply hder.trans (Finset.sum_le_sum _)
    intro i _
    have hn : z-p.location i≠0 := sub_ne_zero.mpr fun e => by rw [e] at hz'; linarith [p.below i]
    exact div_le_div_of_nonneg_left (p.pos i).le (sq_pos_of_pos (norm_pos_iff.mpr hn)) (depth_distance (p.below i) hz'.le ht)
  rw [traceDensity,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),
    source_depthTranslate,source_norm hval]
  simp only [isolatedDensity,←Finset.mul_sum]
  convert mul_le_mul_of_nonneg_left hd (show 0≤z.im/‖z-(x:ℂ)‖^2 by positivity) using 1 <;> ring

private theorem depth_trace_integral {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0≤t) (x : ℝ) :
    field (depthTranslate p.value t) x=Complex.I*∫ z,traceDensity (depthTranslate p.value t) x z ∂upperArea := by
  have h := (p.deeper t ht).field_on_boundary x; rw [p.deeper_value] at h; exact h

theorem PickSum.depth_trace_continuous {n : ℕ} (p : PickSum n) (x : ℝ) :
    ContinuousOn (fun t : ℝ => field (depthTranslate p.value t) x) (Ici 0) := by
  let M := fun z => ∑ i, isolatedDensity (p.weight i) (p.location i) x z
  have hM : Integrable M upperArea := integrable_finsetSum _ (fun i _ => (isolatedDensity_integral (p.pos i) (p.below i) x).1)
  intro t ht
  apply ContinuousWithinAt.congr_of_eventuallyEq (f:=fun u => Complex.I*∫ z, traceDensity (depthTranslate p.value u) x z ∂upperArea)
  · apply ContinuousWithinAt.const_mul
    apply tendsto_integral_filter_of_dominated_convergence M _ _ hM _
    · filter_upwards [self_mem_nhdsWithin (s:=Ici (0:ℝ)) (a:=t)] with u hu
      have hi := (p.deeper u hu).traceDensity_integrable x; rw [p.deeper_value hu] at hi
      exact hi.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin (s:=Ici (0:ℝ)) (a:=t)] with u hu
      filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
      exact p.trace_depth_majorant hu hz x
    · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
      simp only [traceDensity,source_depthTranslate]
      apply Filter.Tendsto.const_mul
      have hmap : ContinuousOn (fun u : ℝ => z+(u:ℂ)*Complex.I) (Ici 0) := by fun_prop
      apply (p.source_continuousOn.comp hmap _ t ht)
      intro u hu; change 0≤(z+(u:ℂ)*Complex.I).im; simp; linarith [show 0<z.im from hz,show 0≤u from hu]
  · filter_upwards [self_mem_nhdsWithin (s:=Ici (0:ℝ)) (a:=t)] with u hu
    exact depth_trace_integral p hu x
  · exact depth_trace_integral p ht x

end Liu
