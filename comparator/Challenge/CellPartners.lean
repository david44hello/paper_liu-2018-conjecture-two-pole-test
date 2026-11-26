import Challenge.InterpolationCharts

/- Frozen input: Liu/CellPartners.lean -/
noncomputable section
open Set Real
open scoped ComplexConjugate
namespace Liu

def CellLine.partnerTests (L : CellLine) (d v : ℂ → ℂ) (w : ℂ) : Prop :=
  let a := 1/(1+Complex.exp (L.s w))
  let p := -d w*Complex.I
  let q := v w*Complex.exp (-L.angle w*Complex.I)
  let p' := d w*Complex.I
  let q' := v w*Complex.exp (L.angle w*Complex.I)
  1+Complex.exp (L.s w) ≠ 0 ∧
    p.im<0 ∧ (p+q).im<0 ∧ (p+a*q).im<0 ∧
    0<p'.im ∧ 0<(p'+q').im ∧ 0<(p'+a*q').im

end Liu
end
