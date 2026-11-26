import Challenge.QuotientDomain
import Challenge.PickSums

/- Frozen input: Liu/PickNumerator.lean -/
noncomputable section
open Set Polynomial Filter
open scoped Topology
namespace Liu.PickSum

def erasedFactor {n : ℕ} (P : PickSum n) (i : Fin n) : ℂ[X] :=
  ∏ j ∈ Finset.univ.erase i, (X-C (P.location j))

def numeratorPoly {n : ℕ} (P : PickSum n) : ℂ[X] :=
  ∑ i, C (-(P.weight i:ℂ)) * P.erasedFactor i

end Liu.PickSum
end
