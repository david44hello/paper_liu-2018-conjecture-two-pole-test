module

public import Challenge.ReciprocalModel

@[expose] public section

/- Frozen input: Liu/SeparatedNodes.lean -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
structure Liu.PickChart where
  mass : ℂ → ℂ
  left : ℂ → ℂ
  right : ℂ → ℂ

namespace Liu.PickChart

def zeroNode (P : PickChart) (w : ℂ) : ℂ :=
  P.mass w * P.right w + (1-P.mass w) * P.left w

def nodeFactor (p z : ℂ) : ℂ := (z-p)/(z+Complex.I)

def valueFactor (P : PickChart) (w z : ℂ) : ℂ :=
  nodeFactor (P.zeroNode w) z * (nodeFactor (P.left w) z)⁻¹ * (nodeFactor (P.right w) z)⁻¹

end Liu.PickChart
end
