import Liu.PickNumerator
import Liu.PolarLogarithm

noncomputable section
open Set MeasureTheory Filter
open scoped ComplexConjugate
namespace Liu

/-- Sum over the numerator zeros with multiplicity, minus the pole sum. -/
def PickSum.signedNodes {n : ℕ} (P : PickSum n) (f : ℂ → ℂ) : ℂ :=
  (P.numeratorPoly.roots.map f).sum - ∑ j, f (P.location j)

private theorem map_sum_transform (s : Multiset ℂ) (f : ℂ → ℂ) (k : ℂ) :
    (s.map (fun c => k*conj (f c))).sum = k*conj ((s.map f).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons c s ih => simp [ih,mul_add]

theorem PickSum.source_rank_terms {n : ℕ} (P : PickSum n) {w : ℂ} (hw : w∈upper) :
    source P.value w=(Complex.I/2)*∑ i, (-(P.weight i:ℂ))*P.signedNodes (fun c => rankSource (P.location i) c w) := by
  have hn : P.value w≠0 := by intro e; have hp := P.value_im_pos (le_of_lt hw); simp [e] at hp
  have h₁ : source P.value w=(Complex.I/2)*P.value w*conj (deriv P.value w/P.value w) := by
    rw [source,map_div₀]; ring
  have h₂ (i : Fin n) : P.signedNodes (fun c => rankSource (P.location i) c w) =
      (w-P.location i)⁻¹*conj (deriv P.value w/P.value w) := by
    rw [P.log_derivative_by_nodes hw,PickSum.signedNodes,map_sub,map_sum,mul_sub,Finset.mul_sum]
    unfold rankSource
    rw [map_sum_transform]
  simp_rw [h₂,h₁]
  simp only [PickSum.value,pole,div_eq_mul_inv]
  rw [mul_assoc,Finset.sum_mul]; apply congrArg
  apply Finset.sum_congr rfl
  intro i _; ring

private theorem signed_rank_integral {n : ℕ} (P : PickSum n) (i : Fin n) {z : ℂ} (hz : 0≤z.im) :
    let K := fun c w => -(greenResolvent z w)*rankSource (P.location i) c w
    Integrable (fun w => P.signedNodes (fun c => K c w)) upperArea ∧
      (∫ w, P.signedNodes (fun c => K c w) ∂upperArea)=P.signedNodes (fun c => rankField (P.location i) c z) := by
  let K := fun c w => -(greenResolvent z w)*rankSource (P.location i) c w
  have hi (c : ℂ) (hc : c.im<0) : Integrable (K c) upperArea := by
    have M p (hp : p.im<0) : 0≤poleBound 1 p := by unfold poleBound; have := neg_pos.mpr hp; positivity
    simpa only [K,neg_mul,Pi.neg_def] using (resolvent_source_integrable
      (show Measurable (rankSource (P.location i) c) by unfold rankSource; fun_prop)
      (mul_nonneg (M _ (P.below i)) (M _ hc)) (fun _ h => rankSource_decay (P.below i) hc (le_of_lt h)) hz).1.neg
  have he (c : ℂ) : (∫ w, K c w ∂upperArea) = rankField (P.location i) c z := by
    unfold K rankField; simp_rw [neg_mul,integral_neg]
  have hm (s : Multiset ℂ) (hs : ∀ c∈s,c.im<0) :
      Integrable (fun w => (s.map (fun c => K c w)).sum) upperArea ∧
      (∫ w, (s.map (fun c => K c w)).sum ∂upperArea)=(s.map (fun c => rankField (P.location i) c z)).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons c s ih =>
      obtain ⟨hI,hEq⟩ := ih (fun d hd => hs _ (Multiset.mem_cons_of_mem hd))
      have hc := hi c (hs _ (Multiset.mem_cons_self ..))
      simp only [Multiset.map_cons,Multiset.sum_cons]
      exact ⟨hc.add hI,by rw [integral_add hc hI,he,hEq]⟩
  obtain ⟨hI,hEq⟩ := hm P.numeratorPoly.roots P.numerator_roots_below.2
  have hp := integrable_finsetSum Finset.univ (fun j _ => hi (P.location j) (P.below j))
  exact ⟨hI.sub hp,by
    change (∫ w, (P.numeratorPoly.roots.map (fun c => K c w)).sum-∑ j,K (P.location j) w ∂upperArea)=_
    rw [integral_sub hI hp,hEq,integral_finsetSum _ (fun j _ => hi _ (P.below j))]
    simp only [he,PickSum.signedNodes]⟩

private theorem signed_const_mul {n : ℕ} (P : PickSum n) (k : ℂ) (f : ℂ → ℂ) :
    P.signedNodes (fun c => k*f c)=k*P.signedNodes f := by
  unfold PickSum.signedNodes
  rw [mul_sub,Finset.mul_sum,Multiset.sum_map_mul_left]

/-- Appendix D.1, including the evaluation at an upper partner. The zero
multiset is the actual numerator root multiset, counted with multiplicity. -/
theorem PickSum.rational_log_field {n : ℕ} (P : PickSum n) {z : ℂ} (hz : 0≤z.im) :
    field P.value z=(Complex.I/2)*∑ i, (-(P.weight i:ℂ))*
      P.signedNodes (fun c => rationalLogTerm (P.location i) (conj c) z) := by
  let K := fun i c w => -(greenResolvent z w)*rankSource (P.location i) c w
  let J := fun i w => P.signedNodes (fun c => K i c w)
  have hi (i : Fin n) : Integrable (J i) upperArea := (signed_rank_integral P i hz).1
  have formula (i : Fin n) : (∫ w, J i w ∂upperArea)=P.signedNodes (fun c => rationalLogTerm (P.location i) (conj c) z) := by
    rw [show (∫ w, J i w ∂upperArea)=_ from (signed_rank_integral P i hz).2]
    unfold PickSum.signedNodes
    congr 1
    · congr 1
      exact Multiset.map_congr rfl fun c hc => rankField_log_formula (P.below i) (P.numerator_roots_below.2 _ hc) hz
    · exact Finset.sum_congr rfl fun j _ => rankField_log_formula (P.below i) (P.below j) hz
  rw [(P.field_integral_closed hz).2,←integral_neg,←Finset.sum_congr rfl (fun i _ => congrArg (fun t => -(P.weight i:ℂ)*t) (formula i))]
  simp_rw [←integral_const_mul]
  rw [←integral_finsetSum _ (fun i _ => (hi i).const_mul _),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
  rw [P.source_rank_terms hw]
  dsimp only [J,K]
  simp_rw [signed_const_mul,←mul_assoc (-(P.weight _:ℂ)) (-(greenResolvent z w)),mul_comm (-(P.weight _:ℂ)) (-(greenResolvent z w)),
    mul_assoc,←Finset.mul_sum]
  ring

end Liu
