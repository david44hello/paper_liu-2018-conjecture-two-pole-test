module

public import Challenge.Projection
public import Challenge.Bergman
public import Challenge.Mass
public import Challenge.Prefix

@[expose] public section

/- Frozen input: Liu/FinitePart.lean -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Liu

def finitePartExists (S : ℂ → ℂ) : Prop :=
  (∀ R : ℝ, 0<R → IntegrableOn (fun z => k₀*‖S z‖^2-‖field S z‖^2) (halfDisc R) area) ∧
    ∃ D : ℝ, Tendsto (truncatedDeficit S) atTop (𝓝 D)

def energy (F : ℂ → ℂ) : ℝ := ‖asL2 F‖^2

end Liu
end
