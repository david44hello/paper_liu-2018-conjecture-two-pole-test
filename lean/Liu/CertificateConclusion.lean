module

public import Liu.MixedEdgeFlux

@[expose] public section

noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
namespace Liu
open scoped Liu


/-- The analytic bound on the prefix integral for each of the 168 boxes. -/
theorem certified_prefix_integral : Certificate.prefixProperty :=
  Certificate.prefix_of_estimates small_depth_flux_estimate mixed_edge_flux_estimate depth_flux_identity

/-- Theorem 3.5 with the two clauses of the fixed computer certificate as its
only external premise. This applies to unequal and coincident lower poles. -/
theorem pair_deficit_of_certificate (p : Pair) (box : Certificate.boxBounds) :
    k₀*p.mass^2<deficit p.value :=
  pair_deficit_of_two_inputs p box mixed_edge_flux_estimate

/-- Theorem 1.1 with the fixed computer certificate as its sole premise. -/
theorem two_pole_test_of_certificate (p : Pair) (box : Certificate.boxBounds) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2<deficit p.value ∧ p.slope<0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0<ε → ε<ε₀ → p.quotientDomain ε ∧ quotient (critical p ε)<k₀ :=
  two_pole_test_of_two_inputs p box mixed_edge_flux_estimate

end Liu
