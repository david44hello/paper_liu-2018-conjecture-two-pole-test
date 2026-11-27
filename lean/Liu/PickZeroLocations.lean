module

public import Liu.PickNumerator

@[expose] public section

noncomputable section
open Set Polynomial
namespace Liu.PickSum

/-- For a representation with distinct poles the numerator and denominator
have no common zero. In particular the counted numerator roots are zeros
of the original holomorphic rational function off its poles. -/
theorem numerator_at_pole_ne_zero {n : ℕ} (P : PickSum n) (hinj : Function.Injective P.location) (i : Fin n) :
    P.numeratorPoly.eval (P.location i)≠0 := by
  classical
  simp only [numeratorPoly,eval_finsetSum,eval_mul,eval_C,erasedFactor,eval_prod,eval_sub,eval_X]
  rw [Finset.sum_eq_single i]
  · exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (P.pos i).ne'))
      (Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun e =>
        (Finset.ne_of_mem_erase hj) (hinj e).symm)
  · intro j _ hji
    have hi : i∈Finset.univ.erase j := Finset.mem_erase.mpr ⟨hji.symm,Finset.mem_univ _⟩
    rw [Finset.prod_eq_zero hi (sub_self _),mul_zero]
  · simp

theorem numerator_root_iff {n : ℕ} (P : PickSum n) (hinj : Function.Injective P.location) (c : ℂ) :
    c∈P.numeratorPoly.roots ↔ (∀ j, c≠P.location j) ∧ P.value c=0 := by
  have hpoly : P.numeratorPoly ≠ 0 := by
    intro he; have h := P.numerator_degree.2; rw [he,leadingCoeff_zero] at h
    exact (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr P.mass_pos.ne')) h.symm
  rw [mem_roots hpoly]
  change P.numeratorPoly.eval c=0 ↔ _
  constructor
  · intro h
    have hn (j : Fin n) : c≠P.location j := fun e => P.numerator_at_pole_ne_zero hinj j (e ▸ h)
    rw [P.numerator_eval hn] at h
    have hd : P.denominatorPoly.eval c ≠ 0 := by
      simp only [denominatorPoly,eval_prod,eval_sub,eval_X,eval_C]
      exact Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr (hn j)
    exact ⟨hn,(mul_eq_zero.mp h).resolve_right hd⟩
  · rintro ⟨hn,hv⟩; rw [P.numerator_eval hn,hv,zero_mul]

end Liu.PickSum
