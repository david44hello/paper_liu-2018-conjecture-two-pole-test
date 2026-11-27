module

public import Challenge.PairedFlux

@[expose] public section

/- Frozen input: Liu/SinglePartnerFlux.lean -/
noncomputable section
open Set MeasureTheory Filter Real Complex
open scoped Topology ComplexConjugate
namespace Liu

theorem single_partner_integral_zero {p q : ℂ} (hp : p.im<0) (hq : 0<q.im) :
    (∫ x : ℝ, singleDensity p q (x:ℂ))=0 := by sorry

end Liu
end
