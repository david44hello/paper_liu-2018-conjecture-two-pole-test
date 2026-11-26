import Liu.ParameterDiscIntegral

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology
namespace Liu

/-- Schwarz's estimate on an interior disc dominates the slopes by a multiple
of the original majorant. This identifies the derivative under the integral. -/
theorem hasDerivAt_local_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {U : Set ℂ} (hU : IsOpen U) {F : ℂ → α → ℂ} {c : ℂ} (hc : c∈U)
    (hm : ∀ w, AEStronglyMeasurable (F w) μ)
    (hd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => F w t) U)
    {M : α → ℝ} (hI : Integrable M μ) {V : Set ℂ} (hV : V∈𝓝 c)
    (hb : ∀ᵐ t ∂μ, ∀ w∈V, ‖F w t‖≤M t) :
    HasDerivAt (fun w => ∫ t, F w t ∂μ) (∫ t, deriv (fun w => F w t) c ∂μ) c := by
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (hU.mem_nhds hc))
  have hi {w : ℂ} (hw : w∈ball c R) := hI.mono' (hm w) (hb.mono fun t ht => ht w (hball hw).1)
  let Q := fun w t => slope (fun k => F k t) c w
  let D := fun t => deriv (fun k => F k t) c
  have hlim : Tendsto (fun w => ∫ t, Q w t ∂μ) (𝓝[≠] c) (𝓝 (∫ t, D t ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t => 2*M t/R)
    · exact Eventually.of_forall fun w => ((hm w).sub (hm c)).const_smul ((w-c)⁻¹)
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c hR),self_mem_nhdsWithin] with w hw hn
      have hne : w≠c := hn
      filter_upwards [hd,hb] with t ht htM
      have hmap : MapsTo (fun v => F v t) (ball c R) (closedBall (F c t) (2*M t)) := by
        intro v hv
        rw [mem_closedBall_iff_norm]
        linarith [norm_sub_le (F v t) (F c t),htM v (hball hv).1,htM c (hball (mem_ball_self hR)).1]
      simpa only [dslope_of_ne _ hne,Q] using
        Complex.norm_dslope_le_div_of_mapsTo_ball (ht.mono fun v hv => (hball hv).2) hmap hw
    · exact (hI.const_mul 2).div_const R
    · filter_upwards [hd] with t ht
      exact hasDerivAt_iff_tendsto_slope.mp (ht.differentiableAt (hU.mem_nhds hc)).hasDerivAt
  apply hasDerivAt_iff_tendsto_slope.mpr (hlim.congr' ?_)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c hR)] with w hw
  simp only [Q,slope_def_module,integral_smul,integral_sub (hi hw) (hi (mem_ball_self hR))]

end Liu
