module

public import Liu.Bergman
public import Liu.Mass
public import Liu.Prefix

@[expose] public section

noncomputable section
open Set Filter
namespace Liu

/-- Concrete conditions from the outstanding analytic proof and the change of coordinates. -/
def coincidentDeficit : Prop := ∀ (a : ℝ) (w : ℂ), 0 < a → w.im < 0 →
  deficit (pole a w) = singleConstant * a^2

def smallMassDeficit : Prop := ∀ p : Pair, min p.a₁ p.a₂ ≤ max p.a₁ p.a₂/4096 →
  (38/1000:ℝ) * (max p.a₁ p.a₂)^2 < deficit p.value - k₀*p.mass^2

def normalizedRepresentation : Prop := ∀ p : Pair, p.w₁ ≠ p.w₂ →
  ∃ s γ u : ℝ, (s = Real.log (p.a₂/p.a₁) ∨ s = -Real.log (p.a₂/p.a₁)) ∧
    γ ∈ Icc 0 (Real.pi/2) ∧ 0 < u ∧ deficit p.value / p.mass^2 - k₀ = margin s γ u

theorem pair_deficit_of_local_representation (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) (hcoinc : coincidentDeficit)
    (hsmall : smallMassDeficit) (hnorm : p.w₁ ≠ p.w₂ →
      ∃ s γ u : ℝ, (s = Real.log (p.a₂/p.a₁) ∨ s = -Real.log (p.a₂/p.a₁)) ∧
        γ ∈ Icc 0 (Real.pi/2) ∧ 0 < u ∧ deficit p.value / p.mass^2 - k₀ = margin s γ u) :
    k₀*p.mass^2 < deficit p.value := by
  by_cases he : p.w₁=p.w₂
  · rw [p.coincident_value he,hcoinc p.mass p.w₁ p.mass_pos p.hw₁]
    apply mul_lt_mul_of_pos_right _ (sq_pos_of_pos p.mass_pos)
    linarith [single_margin_lower]
  by_cases hm : min p.a₁ p.a₂ ≤ max p.a₁ p.a₂/4096
  · linarith [hsmall p hm, sq_nonneg (max p.a₁ p.a₂)]
  obtain ⟨s,γ,u,hs,hg,hu,eqn⟩ := hnorm he
  have range := log_mass_ratio_bounds p.ha₁ p.ha₂ (lt_of_not_ge hm)
  have hsr : s ∈ Icc (-(25/3:ℝ)) (25/3) := by
    rcases hs with h | h
    · simpa [h] using range
    · rw [h]; constructor <;> linarith [range.1,range.2]
  have hp := Certificate.normalized_margin_pos hbox hflux
    (Certificate.prefix_of_estimates h54 hE4 hflux) hsr hg hu
  exact (lt_div_iff₀ (sq_pos_of_pos p.mass_pos)).mp (by linarith)

theorem pair_deficit_of_inputs (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) (hcoinc : coincidentDeficit)
    (hsmall : smallMassDeficit) (hnorm : normalizedRepresentation) :
    k₀*p.mass^2 < deficit p.value :=
  pair_deficit_of_local_representation p hbox hflux h54 hE4 hcoinc hsmall (hnorm p)

theorem pair_quotient_of_inputs (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) (hcoinc : coincidentDeficit)
    (hsmall : smallMassDeficit) (hnorm : normalizedRepresentation) (hexp : p.expansion) :
    p.slope < 0 ∧ ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      p.quotientDomain ε ∧ quotient (critical p ε) < k₀ :=
  p.eventually_below_of_deficit hexp (pair_deficit_of_inputs p hbox hflux h54 hE4 hcoinc hsmall hnorm)

end Liu
