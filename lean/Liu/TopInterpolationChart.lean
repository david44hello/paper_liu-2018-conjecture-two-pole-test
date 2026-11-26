import Liu.InterpolationCharts

noncomputable section
open Real Set
open scoped Topology ComplexConjugate
namespace Liu

def topCellFlux (L : CellLine) (r : ℝ) : ℝ :=
  let v := reciprocalScale*(1-(L.y₀+L.y₁*r))
  reciprocalScale * v⁻¹ * boundaryFlux (unitDepthSum (L.s₀+L.s₁*r) (L.realAngle r) v)

private theorem top_focus {L : CellLine} {c : ℝ} (hy : L.y₀+L.y₁*c=1) :
    (c:ℂ) ∈ L.topNodes.domain L.massDomain ∧ L.topNodes.fluxExtension c=0 := by
  have hv : L.reciprocal c=0 := by rw [L.reciprocal_real,hy]; simp
  have hl : L.topNodes.left c= -Complex.I := by simp [CellLine.topNodes,CellLine.nodes]
  have hr : L.topNodes.right c= -Complex.I := by simp [CellLine.topNodes,CellLine.nodes,hv]
  have ho : L.topNodes.zeroNode c= -Complex.I := by rw [PickChart.zeroNode,hl,hr]; ring
  have hb : L.topNodes.below c := by unfold PickChart.below; rw [hl,hr,ho]; simp
  have hc : (c:ℂ)∈L.topNodes.domain L.massDomain := by
    exact ⟨⟨L.mass_domain_real c,hb⟩,by simpa only [Complex.conj_ofReal] using And.intro (L.mass_domain_real c) hb⟩
  exact ⟨hc,by rw [L.top_agrees hc,hy]; simp [unitDepth_flux_zero]⟩

/-- In the depth variable the extension crosses the reciprocal-depth zero.
Its value at the focus is the removable value supplied by the divided difference. -/
theorem top_depth_cell_analytic (L : CellLine) (hy : L.y₁ ≠ 0) {E : Set ℂ}
    (hE : E ⊆ L.topNodes.domain L.massDomain) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F E ∧
      ∀ r : ℝ, (r:ℂ)∈E → L.y₀+L.y₁*r ≠ 1 → F r=(topCellFlux L r:ℂ) := by
  let c := (1-L.y₀)/L.y₁
  have hc : L.y₀+L.y₁*c=1 := by dsimp [c]; field_simp; ring
  obtain ⟨hcU,hc₀⟩ := top_focus hc
  have h := L.top_regular
  have hD := (Complex.differentiableOn_dslope (h.isOpen.mem_nhds hcU)).mpr h.flux_analytic.differentiableOn
  refine ⟨fun w => -((L.y₁:ℂ)⁻¹)*dslope L.topNodes.fluxExtension (c:ℂ) w,
    ((hD.const_mul _).analyticOnNhd h.isOpen).mono hE,?_⟩
  intro r hr hy'
  have hrc : r ≠ c := by intro e; rw [e] at hy'; contradiction
  have hne : (r:ℂ) ≠ (c:ℂ) := fun e => hrc (Complex.ofReal_injective e)
  have hs : reciprocalScale ≠ 0 := by unfold reciprocalScale; positivity
  have hd : 1-(L.y₀+L.y₁*r) = -L.y₁*(r-c) := by linarith only [hc]
  dsimp only
  rw [dslope_of_ne _ hne,slope_def_module,hc₀,sub_zero,smul_eq_mul,L.top_agrees (hE hr)]
  unfold topCellFlux
  -- Separate the rational Jacobian from the value of the physical flux.
  push_cast
  have hd' := congrArg Complex.ofReal hd
  push_cast at hd'
  rw [hd']
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hs,Complex.ofReal_ne_zero.mpr hy,sub_ne_zero.mpr hne] <;> ring

/-- For a fixed nonzero reciprocal depth only the mass or the angle varies. -/
theorem top_horizontal_cell_analytic (L : CellLine) (hy : L.y₁ = 0) (hn : L.y₀ ≠ 1) {E : Set ℂ}
    (hE : E ⊆ L.topNodes.domain L.massDomain) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F E ∧ ∀ r : ℝ, (r:ℂ)∈E → F r=(topCellFlux L r:ℂ) := by
  let k := reciprocalScale * (reciprocalScale*(1-L.y₀))⁻¹
  refine ⟨fun w => (k:ℂ)*L.topNodes.fluxExtension w,
    analyticOnNhd_const.mul (L.top_regular.flux_analytic.mono hE),?_⟩
  intro r hr
  dsimp only
  rw [L.top_agrees (hE hr)]
  simp [topCellFlux,k,hy]

/-- Every first-kind sampling point used for the third coordinate in the
two horizontal interpolation tests has strictly positive reciprocal depth. -/
theorem firstKind_reciprocal_pos (n : ℕ) (j : Fin (n+1)) :
    0 < reciprocalScale*(1-Real.cos (firstKindAngle n j)) := by
  have hp : 0<firstKindAngle n j := by unfold firstKindAngle; positivity
  have hπ : firstKindAngle n j<π := by
    unfold firstKindAngle; rw [div_lt_iff₀ (by positivity)]
    have hj : (j:ℝ)≤n := by exact_mod_cast Nat.le_of_lt_succ j.isLt
    nlinarith only [mul_le_mul_of_nonneg_right hj pi_pos.le,pi_pos]
  have hlt := Real.strictAntiOn_cos (show (0:ℝ)∈Icc 0 π from ⟨le_rfl,pi_pos.le⟩) ⟨hp.le,hπ.le⟩ hp
  simp only [cos_zero] at hlt
  exact mul_pos (by unfold reciprocalScale; positivity) (sub_pos.mpr hlt)

end Liu
