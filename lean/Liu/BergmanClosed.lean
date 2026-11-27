module

public import Liu.BergmanEvaluation

@[expose] public section

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace Liu

/-- A square-integrable limit of holomorphic representatives again has a holomorphic
representative. The proof uses disc means for local uniform convergence and an
almost-everywhere convergent subsequence to identify the L² class. -/
theorem analyticVectors_closed : IsClosed analyticVectors := by
  classical
  apply IsSeqClosed.isClosed
  intro X v hX hconv
  choose F hF hd hrep using hX
  have hc := hconv.cauchySeq
  have eval (r : ℝ) (hr : 0<r) (w : ℂ) (hw : r<w.im) (i j : ℕ) :
      r * dist (F i w) (F j w) ≤ dist (X i) (X j) := by
    have h := bergman_evaluation_bound ((hF i).sub (hF j)) ((hd i).sub (hd j)) hr
      (fun _ hw' => ball_below_height hw hw')
    rw [dist_eq_norm,dist_eq_norm,hrep i,hrep j]
    simpa only [Pi.sub_apply,asL2,dif_pos ((hF i).sub (hF j)),MemLp.toLp_sub (hF i) (hF j)] using h
  have strip (r : ℝ) (hr : 0<r) : UniformCauchySeqOn F atTop {w : ℂ | r<w.im} := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc (r*ε) (mul_pos hr hε)
    exact ⟨N,fun i hi j hj w hw => (mul_lt_mul_iff_right₀ hr).mp
      ((eval r hr w hw i j).trans_lt (hN i hi j hj))⟩
  let f := fun z : ℂ => limUnder atTop (fun n : ℕ => F n z)
  have hpt (w : ℂ) (hw : w ∈ upper) : Tendsto (fun n => F n w) atTop (𝓝 (f w)) := by
    change 0<w.im at hw
    have h := (strip (w.im/2) (by linarith)).cauchySeq (x:=w) (show w.im/2<w.im by linarith)
    obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete h
    exact tendsto_nhds_limUnder ⟨y,hy⟩
  have hloc : TendstoLocallyUniformlyOn F f atTop upper := by
    apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
    intro z hz
    change 0<z.im at hz
    let r := z.im/2
    have hr : 0<r := by dsimp [r]; linarith
    have hs : IsOpen {w : ℂ | r<w.im} := isOpen_lt continuous_const Complex.continuous_im
    refine ⟨_,mem_nhdsWithin_of_mem_nhds (hs.mem_nhds (show r<z.im by dsimp [r];linarith)),?_⟩
    exact (strip r hr).tendstoUniformlyOn_of_tendsto (fun w hw => hpt w (hr.trans hw))
  have hdf := hloc.differentiableOn (Eventually.of_forall hd) upper_open
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have allrep : ∀ᵐ z ∂upperArea, ∀ i : ℕ, (X i : PlaneL2) z = F i z := by
    rw [ae_all_iff]
    intro i
    rw [hrep i]
    exact (hF i).coeFn_toLp
  have eqn : f =ᵐ[upperArea] (v:ℂ → ℂ) := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,hae,allrep] with z hz hv hr
    apply tendsto_nhds_unique ((hpt z hz).comp hns.tendsto_atTop)
    change Tendsto (fun i => F (ns i) z) atTop _
    simpa only [hr] using hv
  have hf : MemLp f 2 upperArea := (memLp_congr_ae eqn).mpr (Lp.memLp v)
  refine ⟨f,hf,hdf,?_⟩
  exact Lp.ext (eqn.symm.trans hf.coeFn_toLp.symm)

theorem bergman_projection_range : analyticSubspace = representativeSubspace :=
  projection_range_of_closed analyticVectors_closed

end Liu
