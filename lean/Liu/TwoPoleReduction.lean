import Liu.ShiftCutoff

noncomputable section
open Set Filter
open scoped Topology
namespace Liu

private theorem normalized_deficit_at_pair (p : Pair) (hf : finitePartExists p.value)
    (f : Bool) (d : ℝ) (hd : 0<d) :
    deficit ((((p.shift p.w₁.re).reflect f).dilate d hd).scaleMass (1/p.mass) (one_div_pos.mpr p.mass_pos)).value =
      (1/p.mass)^2*deficit p.value := by
  let shifted := p.shift p.w₁.re
  have hs := p.shift_deficit hf p.w₁.re
  have ht : Tendsto (truncatedDeficit shifted.value) atTop (𝓝 (deficit p.value)) := by
    simpa only [shifted,hs.2] using finite_part_limit hs.1
  apply Tendsto.limUnder_eq
  change Tendsto (fun R => truncatedDeficit _ R) atTop _
  have h := ((ht.comp (tendsto_id.const_mul_atTop hd)).const_mul ((1/p.mass)^2))
  simpa only [Function.comp_def,id_eq,Pair.scaleMass_value,truncatedDeficit_mass_scale,Pair.dilate_value,
    truncatedDeficit_dilate _ hd,Pair.truncated_reflect,shifted] using h

theorem Pair.representation_of_finite_part (p : Pair) (hf : finitePartExists p.value) (he : p.w₁≠p.w₂) :
    ∃ s γ u : ℝ, (s = Real.log (p.a₂/p.a₁) ∨ s = -Real.log (p.a₂/p.a₁)) ∧
      γ ∈ Icc 0 (Real.pi/2) ∧ 0<u ∧ deficit p.value/p.mass^2-k₀ = margin s γ u := by
  by_cases horder : p.w₂.im ≤ p.w₁.im
  · obtain ⟨γ,hγ,u,hu,eqn⟩ := ordered_representation_of_coordinate_identity p
      (normalized_deficit_at_pair p hf) horder he.symm
    exact ⟨_,γ,u,Or.inl rfl,hγ,hu,eqn⟩
  · obtain ⟨γ,hγ,u,hu,eqn⟩ := ordered_representation_of_coordinate_identity p.swap
      (normalized_deficit_at_pair p.swap (by simpa only [Pair.swap_value] using hf)) (le_of_not_ge horder) he
    refine ⟨Real.log (p.a₁/p.a₂),γ,u,Or.inr ?_,hγ,hu,?_⟩
    · rw [Real.log_div p.ha₁.ne' p.ha₂.ne',Real.log_div p.ha₂.ne' p.ha₁.ne']; ring
    · rw [Pair.swap_value] at eqn
      simpa only [Pair.mass,Pair.swap,add_comm] using eqn

/-- In the strict two-pole test, coordinate invariance follows from existence of
the radial finite part of this pair alone. No assumption on any other pair's finite part is needed. -/
theorem two_pole_test_of_finite_part (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) (hcoinc : coincidentDeficit)
    (hsmall : smallMassDeficit) (hfinite : finitePartExists p.value)
    (hnum : Tendsto (fun ε => residual (critical p ε)) (𝓝[>] 0) (𝓝 (k₀*p.mass^2-deficit p.value))) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2 < deficit p.value ∧ p.slope < 0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → p.quotientDomain ε ∧ quotient (critical p ε) < k₀ := by
  have hd := pair_deficit_of_local_representation p hbox hflux h54 hE4 hcoinc hsmall (p.representation_of_finite_part hfinite)
  exact ⟨finite_part_limit hfinite,hd,p.eventually_below_of_deficit (p.slope_from_energy_limits p.denominator_limit hnum) hd⟩

end Liu
