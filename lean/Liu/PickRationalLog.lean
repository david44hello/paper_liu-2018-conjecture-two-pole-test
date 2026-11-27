module

public import Liu.RationalLogSum
public import Liu.PickZeroLocations

@[expose] public section

noncomputable section
open Set
open scoped ComplexConjugate
namespace Liu

/-- The four printed principal logarithms, with the removable quotient
evaluated by its derivative when the observing point is the upper partner. -/
def physicalLogTerm (p c z : ℂ) : ℂ :=
  (conj (Complex.log (z-c)) - conj (Complex.log (conj p-c)))/(z-p) -
    (if z=conj c then (conj c-p)⁻¹ else
      (Complex.log (z-p)-Complex.log (conj c-p))/(z-conj c))

theorem rationalLogTerm_eq_printed {p c z : ℂ} (hp : p.im<0) (hc : c.im<0) (hz : 0≤z.im) :
    rationalLogTerm p (conj c) z=physicalLogTerm p c z := by
  rw [rationalLogTerm_physical hp hc hz,physicalLogTerm]
  by_cases he : z=conj c
  · subst z
    rw [if_pos rfl,dslope_same]
    have hs : conj c-p∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr (by simp; linarith))
    have h := ((hasDerivAt_id (conj c)).sub_const p).clog hs
    change HasDerivAt (fun w : ℂ => Complex.log (w-p)) (1/(conj c-p)) (conj c) at h
    rw [h.deriv,one_div]
  · rw [if_neg he,dslope_of_ne _ he,slope_def_field]

/-- Lemma D.1 for every distinct-pole Pick sum on the closed half-plane.
The n-1 lower zeros are counted with multiplicity in the first inner sum. -/
theorem PickSum.rational_log_formula {n : ℕ} (P : PickSum n) (hinj : Function.Injective P.location) :
    P.numeratorPoly.roots.card=n-1 ∧
    (∀ c∈P.numeratorPoly.roots, c.im<0) ∧
    (∀ c, c∈P.numeratorPoly.roots ↔ (∀ j, c≠P.location j) ∧ P.value c=0) ∧
    ∀ z : ℂ, 0≤z.im → field P.value z =
      (Complex.I/2)*∑ i, (-(P.weight i:ℂ))*
        ((P.numeratorPoly.roots.map (fun c => physicalLogTerm (P.location i) c z)).sum -
          ∑ j, physicalLogTerm (P.location i) (P.location j) z) := by
  refine ⟨P.numerator_roots_below.1,P.numerator_roots_below.2,P.numerator_root_iff hinj,?_⟩
  intro z hz
  rw [P.rational_log_field hz]
  apply congrArg
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg
  unfold PickSum.signedNodes
  congr 1
  · congr 1
    exact Multiset.map_congr rfl fun c hc => rationalLogTerm_eq_printed (P.below i) (P.numerator_roots_below.2 _ hc) hz
  · exact Finset.sum_congr rfl fun j _ => rationalLogTerm_eq_printed (P.below i) (P.below j) hz

end Liu
