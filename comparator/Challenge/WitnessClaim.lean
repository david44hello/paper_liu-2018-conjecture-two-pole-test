module

public import Challenge.FarFieldClaim
public import Challenge.CanonicalField
public import Challenge.Orthogonality
public import Challenge.Witness

@[expose] public section

/- Frozen input: Liu/WitnessClaim.lean -/
noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate
namespace Liu

theorem PickSum.witness_identity {n : ℕ} (p : PickSum n) :
    isWitness (optimalWitness p.value) ∧ ∀ W : ℂ → ℂ, isWitness W →
      let g := witnessDifference p.value W
      let L := limUnder atTop (truncatedWitness p.value W)
      MemLp g 2 upperArea ∧ Tendsto (truncatedWitness p.value W) atTop (𝓝 (deficit p.value-energy g)) ∧
      L=deficit p.value-energy g ∧ L≤deficit p.value ∧
      (L=deficit p.value ↔ EqOn W (optimalWitness p.value) {z : ℂ | 0≤z.im}) := by sorry

end Liu
end
