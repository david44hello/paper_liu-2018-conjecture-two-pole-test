module

public import Mathlib

@[expose] public section

/- Frozen input: Liu/BoxTypes.lean -/
noncomputable section
namespace Liu.Certificate

inductive Chart where
  | corner | logAngle | largeAngle
  deriving DecidableEq, Repr

structure Cell where
  sLo : ℚ
  sHi : ℚ
  pieces : ℕ
  /-- Integer in millionths printed for the lower endpoint after all low pieces. -/
  displayMicro : ℕ
  deriving DecidableEq, Repr

structure Band where
  chart : Chart
  yLo : ℚ
  yHi : ℚ
  cells : List Cell
  deriving DecidableEq, Repr

structure Box where
  chart : Chart
  yLo : ℚ
  yHi : ℚ
  cell : Cell
  deriving DecidableEq, Repr

def Band.box (r : Band) (c : Cell) : Box := ⟨r.chart, r.yLo, r.yHi, c⟩

noncomputable def Chart.angle (chart : Chart) (q : ℚ) : ℝ :=
  if chart = .logAngle then Real.exp q else q

def Box.contains (b : Box) (s γ : ℝ) : Prop :=
  b.cell.sLo ≤ s ∧ s ≤ b.cell.sHi ∧ b.chart.angle b.yLo ≤ γ ∧ γ ≤ b.chart.angle b.yHi

def Box.logDepth (b : Box) : ℚ :=
  (if b.chart = .largeAngle then -(27 / 2) else -(19 / 2)) - b.cell.pieces

noncomputable def Box.depth (b : Box) : ℝ := Real.exp b.logDepth

def Box.safeLower (b : Box) : ℚ := ((b.cell.displayMicro : ℚ) - 1) / 1000000

end Liu.Certificate
end
