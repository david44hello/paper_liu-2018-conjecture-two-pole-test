import Challenge.SeparatedSource
import Challenge.ReciprocalDisc
import Challenge.ChebyshevAlias

/- Frozen input: Liu/InterpolationCharts.lean -/
noncomputable section
open Real Set
open scoped ComplexConjugate Topology
namespace Liu

structure CellLine where
  s₀ : ℝ
  s₁ : ℝ
  g₀ : ℝ
  g₁ : ℝ
  y₀ : ℝ
  y₁ : ℝ
  logAngle : Bool

def CellLine.s (L : CellLine) (w : ℂ) : ℂ := L.s₀+(L.s₁:ℂ)*w

def CellLine.angle (L : CellLine) (w : ℂ) : ℂ :=
  let g := (L.g₀:ℂ)+(L.g₁:ℂ)*w
  if L.logAngle then Complex.exp g else g

def CellLine.y (L : CellLine) (w : ℂ) : ℂ := L.y₀+(L.y₁:ℂ)*w

def CellLine.realAngle (L : CellLine) (r : ℝ) : ℝ :=
  if L.logAngle then exp (L.g₀+L.g₁*r) else L.g₀+L.g₁*r

def CellLine.depth (L : CellLine) (u : ℝ) (w : ℂ) : ℂ := (u:ℂ)*Complex.exp (L.y w-1)

def reciprocalScale : ℝ := exp (-(1/2))/2

def CellLine.reciprocal (L : CellLine) (w : ℂ) : ℂ := (reciprocalScale:ℂ)*(1-L.y w)

end Liu
end
