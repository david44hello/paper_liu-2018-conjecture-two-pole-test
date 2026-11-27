module

public import Challenge.Pick
public import Challenge.PickSums
public import Challenge.Projection

@[expose] public section

/- Frozen input: Liu/BoundaryField.lean -/
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology ComplexConjugate
namespace Liu

def poissonTrace (S : ℂ → ℂ) (x : ℝ) : ℂ :=
  ∫ w in upper, ((2*w.im/‖w-(x:ℂ)‖^2:ℝ):ℂ)*source S w ∂area

theorem PickSum.field_on_boundary {n : ℕ} (p : PickSum n) (x : ℝ) :
    field p.value x = Complex.I*poissonTrace p.value x := by sorry

end Liu
end
