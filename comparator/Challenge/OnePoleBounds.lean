module

public import Challenge.OnePoleWitness
public import Challenge.SingleTrace
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/- Frozen input: Liu/OnePoleBounds.lean -/
noncomputable section
open Set Real
namespace Liu

theorem singlePole_optimalWitness (x : ℝ) {a b : ℝ} (ha : 0<a) (hb : 0<b)
    {z : ℂ} (hz : 0≤z.im) :
    optimalWitness (pole a ((x:ℂ)-(b:ℂ)*Complex.I)) z=singleWitness ((z-(x:ℂ))/(b:ℂ)) := by sorry

theorem singlePole_witness_bounds (x : ℝ) {a b : ℝ} (ha : 0<a) (hb : 0<b)
    {z : ℂ} (hz : 0≤z.im) :
    let S := pole a ((x:ℂ)-(b:ℂ)*Complex.I)
    let D := ((S z).arg:ℂ)-optimalWitness S z
    ‖D‖≤π/2+log 2 ∧ π/2+log 2<2.264 ∧ |D.re|<2.264 ∧ |k₀-‖D‖^2|<4.304 := by sorry

end Liu
end
