module

public import Challenge.Cover
public import Mathlib
public import Challenge.Pick

@[expose] public section

/- Frozen input: Liu/Beta.lean -/
noncomputable section
namespace Liu.Certificate

def Box.maxMassLog (b : Box) : ℚ := max b.cell.sHi (-b.cell.sLo)

def Box.muMin (b : Box) : ℝ := 1/(1 + Real.exp b.maxMassLog)

def Box.aMin (b : Box) : ℝ := normalMass b.cell.sHi

def Box.generalBeta (b : Box) : ℝ :=
  2^34 / b.muMin^2 * b.depth * (2 + Real.log (1/b.depth))

def Box.mixedBeta (b : Box) : ℝ :=
  let sn := Real.sin (b.chart.angle b.yLo)
  b.depth * (64/sn^4 * (1+Real.log (1/b.depth)) + 4096/(b.aMin^2 * sn^8))

def Box.beta (b : Box) : ℝ :=
  if (53/100:ℝ) ≤ b.chart.angle b.yLo then min b.generalBeta b.mixedBeta else b.generalBeta

end Liu.Certificate
end
