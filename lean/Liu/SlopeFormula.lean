import Liu.ExteriorIntegral
import Liu.FinitePartLaws

noncomputable section
open Set MeasureTheory Filter Real Metric
open scoped Topology
namespace Liu

theorem PickSum.frozen_numerator_limit {n : ℕ} (p : PickSum n) :
    Tendsto (fun t : ℝ => ∫ z, p.frozenDensity t z ∂upperArea) (𝓝[>] 0) (𝓝 (k₀*p.mass^2-deficit p.value)) := by
  obtain ⟨L,hL,happrox⟩ := p.frozen_integral_approximation
  let H := fun R : ℝ => L*((∫ z, logTail z ∂upperArea)-(∫ z in halfDisc R, logTail z ∂area))
  have hH : Tendsto H atTop (𝓝 0) := by
    simpa [H] using ((halfDisc_integral_limit logTail_integrable).const_sub (∫ z, logTail z ∂upperArea)).const_mul L
  have hD := finite_part_limit p.finite_part.1
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε3 : 0<ε/3 := by linarith
  obtain ⟨R,hR,hA,hB⟩ := ((eventually_ge_atTop (3:ℝ)).and ((hH.eventually_lt_const hε3).and (Metric.tendsto_nhds.mp hD (ε/3) hε3))).exists
  let M := fun t : ℝ => p.mass^(2+2*t)*((angularEnergy t-k₀)/(2*t))*R^(-2*t)
  let I := fun t : ℝ => ∫ z in halfDisc R, p.frozenDensity t z ∂area
  have hc : Tendsto I (𝓝[>] 0) (𝓝 (-truncatedDeficit p.value R)) := p.compact_frozen_energy_limit R
  have hm : Tendsto M (𝓝[>] 0) (𝓝 (k₀*p.mass^2)) := exterior_model_limit p.mass_pos (by linarith)
  have hsmall := (h0.mul_const π).eventually_lt_const (show (0:ℝ)*π<1/2 by norm_num)
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),h0.eventually_lt_const zero_lt_one,
    hsmall,Metric.tendsto_nhds.mp (hc.add hm) (ε/3) hε3] with t ht ht1 hs hclose
  have he := happrox R hR t ht ht1 hs.le
  change |(∫ z, p.frozenDensity t z ∂upperArea)-(I t+M t)|≤H R at he
  have h1 : dist (∫ z, p.frozenDensity t z ∂upperArea) (I t+M t) < ε/3 := he.trans_lt hA
  have h2 : dist (-truncatedDeficit p.value R+k₀*p.mass^2) (k₀*p.mass^2-deficit p.value)<ε/3 := by
    rw [Real.dist_eq,show -truncatedDeficit p.value R+k₀*p.mass^2-(k₀*p.mass^2-deficit p.value) =
      deficit p.value-truncatedDeficit p.value R by ring,abs_sub_comm]
    exact hB
  have hh₁ := dist_triangle (∫ z, p.frozenDensity t z ∂upperArea) (I t+M t) (k₀*p.mass^2-deficit p.value)
  have hh₂ := dist_triangle (I t+M t) (-truncatedDeficit p.value R+k₀*p.mass^2) (k₀*p.mass^2-deficit p.value)
  change dist (I t+M t) (-truncatedDeficit p.value R+k₀*p.mass^2)<ε/3 at hclose
  linarith only [hh₁,hh₂,h1,h2,hclose]

theorem PickSum.residual_limit {n : ℕ} (p : PickSum n) :
    Tendsto (fun t : ℝ => residual (p.power (1+t))) (𝓝[>] 0) (𝓝 (k₀*p.mass^2-deficit p.value)) := by
  obtain ⟨C,hC,h⟩ := p.physical_freezing_cost
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have ht : ∀ᶠ t in 𝓝[>] (0:ℝ), t∈Ioo (0:ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),h0.eventually_lt_const zero_lt_one] with t h1 h2 using ⟨h1,h2⟩
  let J := fun t : ℝ => ∫ z, p.frozenDensity t z ∂upperArea
  have hdiff : Tendsto (fun t : ℝ => J t-residual (p.power (1+t))) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a:=fun t => C*t) _ (by simpa using h0.const_mul C)
    filter_upwards [ht] with t hh
    dsimp [J,residual]
    rw [(p.frozen_density_integral hh.1 hh.2).2,sub_sub_sub_cancel_right]
    exact h t hh
  have hlim := p.frozen_numerator_limit.sub hdiff
  simpa [J] using hlim

/-- Proposition 3.3 for every finite nonempty Pick sum. The normalized difference
quotient converges to both printed expressions for the slope. -/
theorem PickSum.slope_formula {n : ℕ} (p : PickSum n) :
    Tendsto (fun t : ℝ => (quotient (p.power (1+t))-k₀)/t) (𝓝[>] 0)
      (𝓝 (2*(k₀-deficit p.value/p.mass^2))) ∧
    2*(k₀-deficit p.value/p.mass^2) = -2*(deficit p.value/p.mass^2-k₀) := by
  refine ⟨?_,by ring⟩
  have hm := p.mass_pos
  have hh := p.residual_limit.div p.denominator_limit (by positivity : p.mass^2/2≠0)
  have hval : (k₀*p.mass^2-deficit p.value)/(p.mass^2/2)=2*(k₀-deficit p.value/p.mass^2) := by field_simp
  rw [hval] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
  have hn := p.powerL2_norm_pos (by linarith [show 0<t from ht] : 1<1+t)
  dsimp [residual,energy,quotient]
  field_simp [hn.ne',(show 0<t from ht).ne']

theorem PickSum.slope_remainder {n : ℕ} (p : PickSum n) :
    Tendsto (fun t : ℝ => (quotient (p.power (1+t))-k₀-
      (2*(k₀-deficit p.value/p.mass^2))*t)/t) (𝓝[>] 0) (𝓝 0) := by
  have h := p.slope_formula.1.sub_const (2*(k₀-deficit p.value/p.mass^2))
  rw [sub_self] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
  field_simp [(show 0<t from ht).ne'] <;> ring

theorem PickSum.quotient_side_of_margin {n : ℕ} (p : PickSum n) :
    (0<deficit p.value/p.mass^2-k₀ → ∀ᶠ t in 𝓝[>] (0:ℝ), quotient (p.power (1+t))<k₀) ∧
    (deficit p.value/p.mass^2-k₀<0 → ∀ᶠ t in 𝓝[>] (0:ℝ), k₀<quotient (p.power (1+t))) := by
  have h := p.slope_formula.1
  constructor
  · intro hm
    filter_upwards [h.eventually_lt_const (show 2*(k₀-deficit p.value/p.mass^2)<0 by linarith),
      self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t hq ht
    exact sub_neg.mp (by simpa using (div_lt_iff₀ (show 0<t from ht)).mp hq)
  · intro hm
    filter_upwards [h.eventually_const_lt (show 0<2*(k₀-deficit p.value/p.mass^2) by linarith),
      self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t hq ht
    exact sub_pos.mp (by simpa using (lt_div_iff₀ (show 0<t from ht)).mp hq)

theorem two_pole_test_of_six_inputs (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) (hcoinc : coincidentDeficit) (hsmall : smallMassDeficit) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2 < deficit p.value ∧ p.slope < 0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → p.quotientDomain ε ∧ quotient (critical p ε) < k₀ := by
  apply two_pole_test_of_seven_inputs p hbox hflux h54 hE4 hcoinc hsmall
  have hh := p.toPick.residual_limit
  have hm : p.toPick.mass=p.mass := by simp [PickSum.mass,Pair.mass,Pair.toPick,Fin.sum_univ_two]
  have hv : p.toPick.value=p.value := by funext z; simp [PickSum.value,Pair.value,Pair.toPick,Fin.sum_univ_two]
  simpa only [Pair.toPick_power,hm,hv] using hh

end Liu
