import Challenge.PickNumerator
import Challenge.SeparatedSource
import Mathlib.Analysis.Analytic.IsolatedZeros
import Challenge.OnePoleBounds

/- Frozen input: Liu/PickRationalLog.lean -/
noncomputable section
open Set
open scoped ComplexConjugate
namespace Liu

def physicalLogTerm (p c z : ℂ) : ℂ :=
  (conj (Complex.log (z-c)) - conj (Complex.log (conj p-c)))/(z-p) -
    (if z=conj c then (conj c-p)⁻¹ else
      (Complex.log (z-p)-Complex.log (conj c-p))/(z-conj c))

theorem PickSum.rational_log_formula {n : ℕ} (P : PickSum n) (hinj : Function.Injective P.location) :
    P.numeratorPoly.roots.card=n-1 ∧
    (∀ c∈P.numeratorPoly.roots, c.im<0) ∧
    (∀ c, c∈P.numeratorPoly.roots ↔ (∀ j, c≠P.location j) ∧ P.value c=0) ∧
    ∀ z : ℂ, 0≤z.im → field P.value z =
      (Complex.I/2)*∑ i, (-(P.weight i:ℂ))*
        ((P.numeratorPoly.roots.map (fun c => physicalLogTerm (P.location i) c z)).sum -
          ∑ j, physicalLogTerm (P.location i) (P.location j) z) := by sorry

end Liu
end
