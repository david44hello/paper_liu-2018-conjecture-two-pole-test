module

public import Challenge.Witness
public import Challenge.RadialEnergy

@[expose] public section

/- Frozen input: Liu/AngularDeficit.lean -/
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

def angularDeficit (θ : ℝ) := k₀ - (π/2-θ)^2

def leadingDeficit (m : ℝ) (z : ℂ) := m^2*radialTail 2 z*angularDeficit z.arg

end Liu
end
