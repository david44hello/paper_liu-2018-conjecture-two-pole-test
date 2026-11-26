import Challenge.PickSums

/- Frozen input: Liu/QuotientDomain.lean -/
noncomputable section
open Set MeasureTheory
namespace Liu

def Pair.toPick (p : Pair) : PickSum 2 where
  nonempty := by decide
  weight := ![p.a₁,p.a₂]
  location := ![p.w₁,p.w₂]
  pos := by intro i; fin_cases i <;> simp [p.ha₁,p.ha₂]
  below := by intro i; fin_cases i <;> simp [p.hw₁,p.hw₂]

end Liu
end
