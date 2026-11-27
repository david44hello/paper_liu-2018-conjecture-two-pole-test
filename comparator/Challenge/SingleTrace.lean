module

public import Challenge.BoundaryField
public import Challenge.PoissonLine

@[expose] public section

/- Frozen input: Liu/SingleTrace.lean -/
noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

def isolatedTrace (a b x : ℝ) : ℝ := ∫ t in Ioi b, poissonLine a t x/(t+b)

theorem field_single_pole (a x : ℝ) {m b : ℝ} (hm : 0 < m) (hb : 0 < b) :
    field (pole m ((a:ℂ)-(b:ℂ)*Complex.I)) x = -(m:ℂ)*(isolatedTrace a b x:ℂ) := by sorry

theorem isolatedTrace_nonneg (a x : ℝ) {b : ℝ} (hb : 0 < b) : 0 ≤ isolatedTrace a b x := by sorry

end Liu
end
