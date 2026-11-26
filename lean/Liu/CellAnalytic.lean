import Liu.TopCollision
import Liu.ChebyshevEllipse
import Liu.CellPartners

noncomputable section
open Set Real Filter
open scoped Topology
namespace Liu

/-- Holding the depth coordinate fixed includes the top focus. Its true
physical reciprocal-depth limit, even with varying mass or angle, is zero. -/
theorem top_fixed_depth_analytic (L : CellLine) (hy : L.y₁=0) {E : Set ℂ}
    (hE : E ⊆ L.topNodes.domain L.massDomain) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F E ∧ ∀ r : ℝ, (r:ℂ)∈E → F r=(topCellFlux L r:ℂ) := by
  by_cases hn : L.y₀=1
  · exact ⟨fun _ => 0,analyticOnNhd_const,fun r _ => by simp [topCellFlux,hy,hn]⟩
  · exact top_horizontal_cell_analytic L hy hn hE

/-- In the depth direction the complex extension takes the actual physical
limiting value at the focus, with both horizontal coordinates held fixed. -/
theorem top_varying_depth_analytic (L : CellLine) (hy : L.y₁ ≠ 0) (hs : L.s₁=0) (hg : L.g₁=0)
    {E : Set ℂ} (hE : E ⊆ L.topNodes.domain L.massDomain) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F E ∧ ∀ r : ℝ, (r:ℂ)∈E → F r=(topCellFlux L r:ℂ) := by
  let U := L.topNodes.domain L.massDomain
  obtain ⟨F,hF,he⟩ := top_depth_cell_analytic L hy (E:=U) Subset.rfl
  refine ⟨F,hF.mono hE,?_⟩
  intro r hr
  by_cases hfocus : L.y₀+L.y₁*r=1
  · let γ := L.realAngle r
    have angle (t : ℝ) : L.realAngle t = γ := by simp [γ,CellLine.realAngle,hg]
    let v := fun t : ℝ => reciprocalScale*(1-(L.y₀+L.y₁*t))
    have hv : v r=0 := by simp [v,hfocus]
    have hnear : ∀ᶠ t : ℝ in 𝓝 r, (t:ℂ)∈U :=
      Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (L.top_regular.isOpen.mem_nhds (hE hr))
    have hvlim : Tendsto v (𝓝 r) (𝓝 0) := hv ▸ (show ContinuousAt v r by dsimp [v]; fun_prop).tendsto
    have hlim := (top_focus_limit L.s₀ γ).comp hvlim
    have hR : Tendsto (topCellFlux L) (𝓝 r) (𝓝 0) := by
      have eq : topCellFlux L = fun t : ℝ => reciprocalScale*
          ((v t)⁻¹*boundaryFlux (unitDepthSum L.s₀ γ (v t))) := by
        funext t; simp [topCellFlux,hs,angle,v,mul_assoc]
      rw [eq]
      simpa only [Function.comp_def,mul_zero] using (tendsto_const_nhds (x:=reciprocalScale)).mul hlim
    have hCe : Tendsto (fun t : ℝ => (topCellFlux L t:ℂ)) (𝓝[≠] r) (𝓝 0) :=
      by simpa only [Function.comp_def,Complex.ofReal_zero] using
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hR).mono_left nhdsWithin_le_nhds
    have hFe : Tendsto (fun t : ℝ => F t) (𝓝[≠] r) (𝓝 (F r)) :=
      ((hF _ (hE hr)).continuousAt.comp Complex.continuous_ofReal.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have eqv : (fun t : ℝ => (topCellFlux L t:ℂ)) =ᶠ[𝓝[≠] r] (fun t : ℝ => F t) := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht htr
      have hn : L.y₀+L.y₁*t ≠ 1 := by
        intro e; apply htr
        exact mul_left_cancel₀ hy (show L.y₁*t=L.y₁*r by linarith)
      exact (he t ht hn).symm
    have heq := tendsto_nhds_unique hFe (hCe.congr' eqv)
    simpa [topCellFlux,hfocus] using heq
  · exact he r (hE hr) hfocus

/-- Lemma 6.6 on the closed Bernstein regions. The affine line may vary
mass, linear angle, logarithmic angle, or the depth coordinate. -/
theorem interpolation_cell_analytic (L : CellLine) (u ρ : ℝ)
    (axis : L.y₁=0 ∨ L.s₁=0 ∧ L.g₁=0) :
    ((∀ w∈bernsteinEllipse ρ, L.partnerTests (L.depth u) (fun _ => 1) w) →
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (bernsteinEllipse ρ) ∧
        ∀ t : ℝ, (t:ℂ)∈bernsteinEllipse ρ → F t =
          ((u*exp (L.y₀+L.y₁*t-1)*flux (L.s₀+L.s₁*t) (L.realAngle t)
            (u*exp (L.y₀+L.y₁*t-1)):ℝ):ℂ)) ∧
    ((∀ w∈bernsteinEllipse ρ, L.partnerTests (fun _ => 1) L.reciprocal w) →
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (bernsteinEllipse ρ) ∧
        ∀ t : ℝ, (t:ℂ)∈bernsteinEllipse ρ → F t=(topCellFlux L t:ℂ)) := by
  refine ⟨fun h => cell_flux_separated L u (fun _ hw => (L.cell_partner_tests u _).mpr (h _ hw)),fun h => ?_⟩
  have hE : bernsteinEllipse ρ ⊆ L.topNodes.domain L.massDomain := fun _ hw => (L.top_partner_tests _).mpr (h _ hw)
  by_cases hy : L.y₁=0
  · exact top_fixed_depth_analytic L hy hE
  · obtain ⟨hs,hg⟩ := axis.resolve_left hy
    exact top_varying_depth_analytic L hy hs hg hE

end Liu
