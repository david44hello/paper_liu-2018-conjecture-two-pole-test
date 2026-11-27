module

public import Liu.Comparability

@[expose] public section

noncomputable section
open Set Polynomial Filter
open scoped Topology
namespace Liu.PickSum

def denominatorPoly {n : ℕ} (P : PickSum n) : ℂ[X] := ∏ j, (X-C (P.location j))

def erasedFactor {n : ℕ} (P : PickSum n) (i : Fin n) : ℂ[X] :=
  ∏ j ∈ Finset.univ.erase i, (X-C (P.location j))

def numeratorPoly {n : ℕ} (P : PickSum n) : ℂ[X] :=
  ∑ i, C (-(P.weight i:ℂ)) * P.erasedFactor i

theorem numerator_degree {n : ℕ} (P : PickSum n) :
    P.numeratorPoly.natDegree=n-1 ∧ P.numeratorPoly.leadingCoeff= -(P.mass:ℂ) := by
  have hd (i : Fin n) : (P.erasedFactor i).natDegree=n-1 := by simp [erasedFactor]
  have hm (i : Fin n) : (P.erasedFactor i).Monic := monic_prod_X_sub_C _ _
  have hC (i : Fin n) : (P.erasedFactor i).coeff (n-1)=1 := hd i ▸ (hm i).coeff_natDegree
  have hw (i : Fin n) : -(P.weight i:ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (P.pos i).ne')
  have coeff : P.numeratorPoly.coeff (n-1) = -(P.mass:ℂ) := by
    simp [numeratorPoly,finsetSum_coeff,coeff_C_mul,hC,PickSum.mass]
  have dn : P.numeratorPoly.natDegree=n-1 := natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_sum_le_of_forall_le _ _ fun i _ => by rw [natDegree_C_mul (hw i),hd]) (coeff ▸ neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr P.mass_pos.ne'))
  exact ⟨dn,by rwa [←coeff_natDegree,dn]⟩

theorem denominator_roots {n : ℕ} (P : PickSum n) :
    P.denominatorPoly.roots=(Finset.univ : Finset (Fin n)).val.map P.location := by
  simpa only [denominatorPoly,Finset.prod,Multiset.map_map,Function.comp_def] using
    roots_multiset_prod_X_sub_C ((Finset.univ : Finset (Fin n)).val.map P.location)

theorem numerator_eval {n : ℕ} (P : PickSum n) {z : ℂ} (hn : ∀ i, z≠P.location i) :
    P.numeratorPoly.eval z = P.value z * P.denominatorPoly.eval z := by
  simp only [numeratorPoly,eval_finsetSum,eval_mul,eval_C,erasedFactor,eval_prod,eval_sub,eval_X,
    PickSum.value,denominatorPoly,Finset.sum_mul,pole]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.mul_prod_erase Finset.univ (fun j => z-P.location j) (Finset.mem_univ i)]
  field_simp [sub_ne_zero.mpr (hn i)]

theorem numerator_roots_below {n : ℕ} (P : PickSum n) :
    P.numeratorPoly.roots.card=n-1 ∧ ∀ c∈P.numeratorPoly.roots, c.im<0 := by
  refine ⟨(IsAlgClosed.splits P.numeratorPoly).natDegree_eq_card_roots.symm.trans P.numerator_degree.1,?_⟩
  intro c hc
  by_contra! h
  have hn (i : Fin n) : c≠P.location i := fun e => by rw [e] at h; linarith [P.below i]
  have hD : P.denominatorPoly.eval c ≠ 0 := by
    simp only [denominatorPoly,eval_prod,eval_sub,eval_X,eval_C]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hn i))
  have hV : P.value c ≠ 0 := fun e => by have H := P.value_im_pos h; rw [e] at H; simp at H
  exact (mul_ne_zero hV hD) ((P.numerator_eval hn).symm.trans (isRoot_of_mem_roots hc))

theorem log_derivative_by_nodes {n : ℕ} (P : PickSum n) {w : ℂ} (hw : w∈upper) :
    deriv P.value w / P.value w =
      (P.numeratorPoly.roots.map (fun c => (w-c)⁻¹)).sum - ∑ j, (w-P.location j)⁻¹ := by
  have hn {z : ℂ} (hz : z∈upper) (i : Fin n) : z≠P.location i := fun e => by
    have hpos : 0<z.im := hz; rw [e] at hpos; linarith [P.below i]
  have hD {z : ℂ} (hz : z∈upper) : P.denominatorPoly.eval z≠0 := by
    simp only [denominatorPoly,eval_prod,eval_sub,eval_X,eval_C]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hn hz i)
  have hV : P.value w ≠ 0 := by intro e; have H := P.value_im_pos (le_of_lt hw); simp [e] at H
  have hN : P.numeratorPoly.eval w ≠ 0 := (P.numerator_eval (hn hw)) ▸ mul_ne_zero hV (hD hw)
  have he : P.value =ᶠ[𝓝 w] (fun z => P.numeratorPoly.eval z/P.denominatorPoly.eval z) := by
    filter_upwards [upper_open.mem_nhds hw] with z hz
    rw [P.numerator_eval (hn hz),mul_div_cancel_right₀ _ (hD hz)]
  have hd := (P.numeratorPoly.hasDerivAt w).div (P.denominatorPoly.hasDerivAt w) (hD hw)
  rw [(hd.congr_of_eventuallyEq he).deriv,he.eq_of_nhds]
  have h₁ := (IsAlgClosed.splits P.numeratorPoly).eval_derivative_div_eval_of_ne_zero hN
  have h₂ := (IsAlgClosed.splits P.denominatorPoly).eval_derivative_div_eval_of_ne_zero (hD hw)
  rw [P.denominator_roots,Multiset.map_map] at h₂
  rw [show (∑ j, (w-P.location j)⁻¹)=((Finset.univ : Finset (Fin n)).val.map (fun j => (w-P.location j)⁻¹)).sum from rfl]
  simp only [one_div,Function.comp_def] at h₁ h₂
  rw [←h₁,←h₂]
  field_simp [hD hw,hN] <;> ring

end Liu.PickSum
