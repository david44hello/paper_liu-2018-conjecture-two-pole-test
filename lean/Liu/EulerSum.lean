module

public import Liu.Mass
public import Mathlib.Analysis.PSeries

@[expose] public section

noncomputable section
open Set Real Filter Finset
open scoped Topology
namespace Liu

private def reciprocal (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹

private theorem reciprocal_nonneg (n : ℕ) : 0≤reciprocal n := by unfold reciprocal; positivity

private theorem reciprocal_step (a : ℕ) :
    HasSum (fun j : ℕ => reciprocal (j+a)-reciprocal (j+a+1)) (reciprocal a) := by
  have dec (j : ℕ) : 0≤reciprocal (j+a)-reciprocal (j+a+1) := by
    apply sub_nonneg.mpr; unfold reciprocal
    apply inv_anti₀ (by positivity); push_cast; linarith
  apply (hasSum_iff_tendsto_nat_of_nonneg dec _).mpr
  have lim : Tendsto (fun n : ℕ => reciprocal (n+a)) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    change Tendsto (fun n : ℕ => ((n+a:ℕ):ℝ)+1) atTop atTop
    apply tendsto_atTop_mono (f:=fun n : ℕ => (n:ℝ)) _ tendsto_natCast_atTop_atTop
    intro n; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) a]
  have telesc (n : ℕ) : ∑ j ∈ range n, (reciprocal (j+a)-reciprocal (j+a+1)) = reciprocal a-reciprocal (n+a) := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ,ih]; simp only [Nat.succ_add,Nat.succ_eq_add_one]; ring
  simpa only [telesc,sub_zero] using tendsto_const_nhds.sub lim

private def eulerTerm (a b : ℕ) : ℝ := reciprocal a * reciprocal (a+b+1)^2

private theorem euler_row_summable (a : ℕ) :
    Summable (eulerTerm a) ∧ ∑' b, eulerTerm a b ≤ reciprocal a^2 := by
  have hd := (reciprocal_step a).mul_left (reciprocal a)
  have hmajor (b : ℕ) : eulerTerm a b ≤ reciprocal a*(reciprocal (b+a)-reciprocal (b+a+1)) := by
    unfold eulerTerm
    apply mul_le_mul_of_nonneg_left _ (reciprocal_nonneg _)
    rw [Nat.add_comm a b]
    dsimp [reciprocal]
    push_cast
    have hpos : 0<(b:ℝ)+a+1 := by positivity
    have hpos' : 0<(b:ℝ)+a+1+1 := by positivity
    field_simp [hpos.ne',hpos'.ne']
    nlinarith
  have hn (b : ℕ) : 0≤eulerTerm a b := mul_nonneg (reciprocal_nonneg _) (sq_nonneg _)
  have hs := Summable.of_nonneg_of_le hn hmajor hd.summable
  exact ⟨hs,(hs.tsum_le_tsum hmajor hd.summable).trans_eq (hd.tsum_eq.trans (sq _).symm)⟩

private theorem reciprocal_square_summable : Summable (fun n => reciprocal n^2) := by
  have h := (Real.summable_one_div_nat_pow (p:=2)).mpr (by decide)
  have hs := (summable_nat_add_iff 1).mpr h
  simpa [reciprocal,one_div] using hs

private theorem euler_summable : Summable (Function.uncurry eulerTerm) := by
  apply (summable_prod_of_nonneg (fun (p : ℕ×ℕ) => mul_nonneg (reciprocal_nonneg p.1) (sq_nonneg _))).mpr
  exact ⟨fun a => (euler_row_summable a).1,Summable.of_nonneg_of_le
    (fun a => tsum_nonneg fun b => mul_nonneg (reciprocal_nonneg a) (sq_nonneg _))
    (fun a => (euler_row_summable a).2) reciprocal_square_summable⟩

private def triangularTerm (a k : ℕ) : ℝ := if a<k then reciprocal a*reciprocal k^2 else 0

private theorem triangular_row (a : ℕ) :
    HasSum (triangularTerm a) (∑' b, eulerTerm a b) := by
  have h : HasSum (fun b => triangularTerm a (b+(a+1))) (∑' b, eulerTerm a b) := by
    convert (euler_row_summable a).1.hasSum using 1
    funext b; rw [triangularTerm,if_pos (by omega)]
    simp [eulerTerm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  have he : ∑ j ∈ range (a+1), triangularTerm a j=0 := by
    apply sum_eq_zero
    intro j hj; simp [triangularTerm,show ¬a<j by have := mem_range.mp hj; omega]
  apply (hasSum_nat_add_iff' (a+1)).mp
  simpa only [he,sub_zero] using h

private theorem triangular_col (k : ℕ) :
    (∑' a, triangularTerm a k)=(∑ a ∈ range k, reciprocal a)*reciprocal k^2 := by
  rw [tsum_eq_sum (s:=range k) (by intro a ha; simp [triangularTerm,show ¬a<k from fun h => ha (mem_range.mpr h)]),sum_mul]
  apply sum_congr rfl; intro a ha; simp [triangularTerm,mem_range.mp ha]

private theorem triangular_summable : Summable (Function.uncurry triangularTerm) := by
  apply (summable_prod_of_nonneg (f:=Function.uncurry triangularTerm) (fun p => by
    dsimp only [Function.uncurry,triangularTerm]; split
    · exact mul_nonneg (reciprocal_nonneg _) (sq_nonneg _)
    · exact le_rfl)).mpr
  refine ⟨fun a => (triangular_row a).summable,?_⟩
  change Summable (fun a => ∑' k, triangularTerm a k)
  simp_rw [(triangular_row _).tsum_eq]
  exact euler_summable.prod

private theorem euler_triangular :
    (∑' a, ∑' b, eulerTerm a b) = ∑' k, (∑ a ∈ range k, reciprocal a)*reciprocal k^2 := by
  simpa only [(triangular_row _).tsum_eq,triangular_col] using triangular_summable.tsum_comm.symm

private theorem paired_row (a : ℕ) :
    (∑' b, (eulerTerm a b+eulerTerm b a))=(∑ k ∈ range (a+1), reciprocal k)*reciprocal a^2 := by
  have h := (hasSum_sum (s:=range (a+1)) (fun k _ => reciprocal_step k)).mul_right (reciprocal a^2)
  apply Eq.trans _ h.tsum_eq
  apply tsum_congr
  intro b
  have steps (n : ℕ) : (∑ k ∈ range n, (reciprocal (b+k)-reciprocal (b+k+1)))=reciprocal b-reciprocal (b+n) := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ,ih]; simp only [Nat.add_succ]; ring
  rw [steps]
  simp only [eulerTerm,reciprocal,Nat.cast_add,Nat.cast_one]
  have ha : 0<(a:ℝ)+1 := by positivity
  have hb : 0<(b:ℝ)+1 := by positivity
  have hab : 0<(a:ℝ)+b+1+1 := by positivity
  ring_nf
  field_simp
  <;> ring

/-- The Euler double sum in Appendix A.2. Both indices begin at one
in the usual notation; the inner denominator is strictly larger than the outer index. -/
theorem euler_trigamma_tail :
    (∑' n : ℕ, (1/((n:ℝ)+1))*(∑' j : ℕ, 1/((n:ℝ)+j+2)^2)) = ∑' n : ℕ, 1/(n:ℝ)^3 := by
  let S := ∑' a, ∑' b, eulerTerm a b
  have hcomm : (∑' a, ∑' b, eulerTerm b a)=S := euler_summable.tsum_comm
  have hsa : Summable (fun a => ∑' b, eulerTerm a b) := euler_summable.prod
  have hsb : Summable (fun a => ∑' b, eulerTerm b a) := euler_summable.prod_symm.prod
  have hp : ∑' a, ∑' b, (eulerTerm a b+eulerTerm b a)=S+S := by
    have add (a : ℕ) := ((euler_row_summable a).1).tsum_add (show Summable (fun b => eulerTerm b a) from euler_summable.prod_symm.prod_factor a)
    simp_rw [add]; rw [hsa.tsum_add hsb,hcomm]
  have ht : Summable (fun k => (∑ a ∈ range k, reciprocal a)*reciprocal k^2) := by
    have hg : Summable (fun k => ∑' a, triangularTerm a k) := triangular_summable.prod_symm.prod
    simpa only [triangular_col] using hg
  have hh := (Real.summable_one_div_nat_pow (p:=3)).mpr (by decide)
  have hz : Summable (fun a => reciprocal a^3) := by simpa [reciprocal,one_div] using (summable_nat_add_iff 1).mpr hh
  have hζ : (∑' a, reciprocal a^3)=∑' n : ℕ, 1/(n:ℝ)^3 := by
    have h := (hasSum_nat_add_iff' (f:=fun n : ℕ => 1/(n:ℝ)^3) 1).mpr hh.hasSum
    simpa [reciprocal,one_div] using h.tsum_eq
  have he (k : ℕ) : (∑ a ∈ range (k+1), reciprocal a)*reciprocal k^2 =
      (∑ a ∈ range k, reciprocal a)*reciprocal k^2+reciprocal k^3 := by rw [sum_range_succ]; ring
  simp_rw [paired_row,he] at hp
  rw [ht.tsum_add hz,←euler_triangular,hζ] at hp
  change S+(∑' n : ℕ, 1/(n:ℝ)^3)=S+S at hp
  have hgoal : S=∑' n : ℕ, 1/(n:ℝ)^3 := by linarith only [hp]
  apply Eq.trans _ hgoal
  apply tsum_congr; intro n
  rw [←tsum_mul_left]
  apply tsum_congr; intro j
  simp only [eulerTerm,reciprocal,Nat.cast_add,Nat.cast_one,one_div,inv_pow]
  ring

theorem euler_harmonic_summable : Summable (fun k : ℕ =>
    (∑ j ∈ range k, 1/((j:ℝ)+1))/((k:ℝ)+1)^2) := by
  have h : Summable (fun k => ∑' a, triangularTerm a k) := triangular_summable.prod_symm.prod
  simpa only [triangular_col,reciprocal,one_div,div_eq_mul_inv,one_mul,inv_pow] using h

theorem reciprocal_square_tail (n : ℕ) :
    (∑' j : ℕ, 1/((n:ℝ)+j+2)^2) ≤ 1/((n:ℝ)+1) := by
  have h := (euler_row_summable n).2
  have hfun (j : ℕ) : eulerTerm n j = reciprocal n*(1/((n:ℝ)+j+2)^2) := by
    dsimp only [eulerTerm,reciprocal]; push_cast; rw [show (n:ℝ)+j+1+1=n+j+2 by ring,one_div,inv_pow]
  simp_rw [hfun,tsum_mul_left] at h
  rw [sq] at h
  simpa only [reciprocal,one_div] using (mul_le_mul_iff_right₀ (show 0<reciprocal n by unfold reciprocal; positivity)).mp h

end Liu
