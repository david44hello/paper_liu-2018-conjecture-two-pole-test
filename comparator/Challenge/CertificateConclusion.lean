module

public import Challenge.MixedEdgeFlux

@[expose] public section

/- Frozen input: Liu/CertificateConclusion.lean -/
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
namespace Liu
open scoped Liu


theorem certified_prefix_integral : Certificate.prefixProperty := by sorry

theorem pair_deficit_of_certificate (p : Pair) (box : Certificate.boxBounds) :
    k₀*p.mass^2<deficit p.value := by sorry

theorem two_pole_test_of_certificate (p : Pair) (box : Certificate.boxBounds) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2<deficit p.value ∧ p.slope<0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0<ε → ε<ε₀ → p.quotientDomain ε ∧ quotient (critical p ε)<k₀ := by sorry

end Liu
end
