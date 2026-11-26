import Liu.Gluing
import Liu.Mass

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Liu

/-- Large-depth specialization of the merged-pole lower estimate. -/
def deepCluster : Prop := ∀ s γ T : ℝ, γ ∈ Icc 0 (Real.pi/2) → 4 ≤ T →
  (singleConstant-k₀) - 4.05/(T*(T-1)) ≤ margin s γ T

theorem anchor_of_cluster_and_flux (hc : deepCluster) (hf : Certificate.fluxIdentity)
    {s γ u L : ℝ} (hg : γ ∈ Icc 0 (Real.pi/2)) (hu : 0 < u)
    (conv : Tendsto (fun T => ∫ t in u..T, flux s γ t) atTop (𝓝 L)) :
    (singleConstant-k₀)-L ≤ margin s γ u := by
  have hden : Tendsto (fun T : ℝ => T*(T-1)) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ (by simpa [sub_eq_add_neg] using (tendsto_atTop_add_const_right atTop (-1:ℝ) tendsto_id))
  have er : Tendsto (fun T : ℝ => (4.05:ℝ)/(T*(T-1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hl : Tendsto (fun T : ℝ => (singleConstant-k₀)-4.05/(T*(T-1)) -
      ∫ t in u..T,flux s γ t) atTop (𝓝 ((singleConstant-k₀)-L)) := by
    simpa using ((tendsto_const_nhds (x := singleConstant-k₀)).sub er).sub conv
  apply le_of_tendsto hl
  filter_upwards [eventually_ge_atTop 4,eventually_ge_atTop u] with T h4 hT
  rw [(hf s γ hg u T hu hT).2]
  exact sub_le_sub_right (hc s γ T hg h4) _

/-- Append the improper last cell to a finite chain of genuine signed flux integrals. -/
theorem chain_suffix_limit {f : ℝ → ℝ} {nodes : ℕ → ℝ} {i n : ℕ} (hin : i ≤ n)
    {u L : ℝ} (hfirst : IntervalIntegrable f volume u (nodes i))
    (hint : ∀ k ∈ Set.Ico i n, IntervalIntegrable f volume (nodes k) (nodes (k+1)))
    (htop : ∀ T : ℝ, nodes n ≤ T → IntervalIntegrable f volume (nodes n) T)
    (conv : Tendsto (fun T => ∫ t in nodes n..T, f t) atTop (𝓝 L)) :
    Tendsto (fun T => ∫ t in u..T, f t) atTop
      (𝓝 ((∫ t in u..nodes i, f t) + (∑ k ∈ Finset.Ico i n, ∫ t in nodes k..nodes (k+1), f t) + L)) := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals_Ico hin hint
  have hadj : IntervalIntegrable f volume (nodes i) (nodes n) :=
    IntervalIntegrable.trans_iterate_Ico hin hint
  rw [hsum,intervalIntegral.integral_add_adjacent_intervals hfirst hadj]
  apply Filter.Tendsto.congr' _ (conv.const_add _)
  filter_upwards [eventually_ge_atTop (nodes n)] with T hT
  exact intervalIntegral.integral_add_adjacent_intervals (hfirst.trans hadj) (htop T hT)

end Liu
