module

public import Challenge.FirstOrderMajorant
public import Challenge.FirstOrderExpansion

@[expose] public section

/- Frozen input: Liu/SmallFirstOrder.lean -/
noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped Topology ComplexConjugate
namespace Liu

def mixedPoleIntegral (p q : ℂ) (R : ℝ) :=
  let A := pole 1 p
  let B := pole 1 q
  ∫ z in halfDisc R, ((k₀:ℂ)*A z*conj (B z)-field A z*conj (field B z)).re ∂area

def smallMassFirstOrder (p q : ℂ) :=
  let A := pole 1 p
  let B := pole 1 q
  2*limUnder atTop (mixedPoleIntegral p q) -
    2*(∫ z, field A z*conj (linearBlend (A z) (B z)) ∂upperArea).re

theorem smallMassFirstOrder_formula {q : ℂ} (hq : q.im<0) :
    let p := -Complex.I
    let Y := firstOrderIntegrand p q
    let J := mixedPoleIntegral p q
    Integrable Y upperArea ∧ Tendsto J atTop (𝓝 (limUnder atTop J)) ∧
    smallMassFirstOrder p q=2*singleConstant+2*(∫ z, Y z ∂upperArea).re ∧
    |smallMassFirstOrder p q-2*singleConstant|≤167 := by sorry

end Liu
end
