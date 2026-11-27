module

public import Liu.Mass
public import Mathlib.Analysis.PSeries

@[expose] public section

noncomputable section
open Set Real Filter Finset
open scoped Topology
namespace Liu

private def tailMajorant (n : ℕ) : ℝ := 1/(2*(n:ℝ)*(n+1))

private theorem tailMajorant_step {N : ℕ} (hN : 0<N) :
    HasSum (fun j : ℕ => tailMajorant (j+N)-tailMajorant (j+N+1)) (tailMajorant N) := by
  have hn (j : ℕ) : 0<((j+N:ℕ):ℝ) := Nat.cast_pos.mpr (by omega)
  have hd (j : ℕ) : 0≤tailMajorant (j+N)-tailMajorant (j+N+1) := by
    dsimp only [tailMajorant]; apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    rw [Nat.cast_add_one]; nlinarith [hn j]
  have hi : Tendsto (fun j : ℕ => ((j+N:ℕ):ℝ)⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    apply tendsto_atTop_mono (f:=fun n : ℕ => (n:ℝ)) _ tendsto_natCast_atTop_atTop
    intro j; exact_mod_cast (by omega : j≤j+N)
  have ht : Tendsto (fun j : ℕ => tailMajorant (j+N)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun j => by unfold tailMajorant; positivity) _ hi
    exact Eventually.of_forall fun j => by
      unfold tailMajorant; rw [←one_div]; apply one_div_le_one_div_of_le (hn j)
      nlinarith [hn j,sq_nonneg ((j+N:ℕ):ℝ)]
  apply (hasSum_iff_tendsto_nat_of_nonneg hd _).mpr
  have he (k : ℕ) : ∑ j ∈ range k, (tailMajorant (j+N)-tailMajorant (j+N+1))=tailMajorant N-tailMajorant (k+N) := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ,ih]; simp only [Nat.succ_add,Nat.succ_eq_add_one]; ring
  simpa only [he,sub_zero] using tendsto_const_nhds.sub ht

private theorem zeta_tail_bounds {N : ℕ} (hN : 0<N) :
    let S := ∑ k ∈ range (N+1), 1/(k:ℝ)^3
    let Z := ∑' n : ℕ, 1/(n:ℝ)^3
    S+(1-1/((N:ℝ)+1)^2)*tailMajorant N≤Z ∧ Z≤S+tailMajorant N := by
  dsimp only
  have hz := ((Real.summable_one_div_nat_pow (p:=3)).mpr (by decide)).hasSum
  have ht := (hasSum_nat_add_iff' (f:=fun k : ℕ => 1/(k:ℝ)^3) (N+1)).mpr hz
  have h := tailMajorant_step hN
  let D := fun j => tailMajorant (j+N)-tailMajorant (j+N+1)
  let k := 1-1/((N:ℝ)+1)^2
  have bounds (j : ℕ) : k*D j≤1/((j+(N+1):ℕ):ℝ)^3 ∧ 1/((j+(N+1):ℕ):ℝ)^3≤D j := by
    let a : ℝ := ((j+N:ℕ):ℝ)
    have hp : 0<a := Nat.cast_pos.mpr (by omega)
    have h1 : 0<a+1 := by positivity
    have h2 : 0<a+2 := by positivity
    have he : D j=1/(a*(a+1)*(a+2)) := by
      dsimp only [D,tailMajorant]; rw [Nat.cast_add_one]; change 1/(2*a*(a+1))-1/(2*(a+1)*(a+1+1))=_
      rw [show a+1+1=a+2 by ring]; field_simp [hp.ne',h1.ne',h2.ne']; ring
    rw [←Nat.add_assoc,Nat.cast_add_one,he]
    change k*(1/(a*(a+1)*(a+2)))≤1/(a+1)^3 ∧ 1/(a+1)^3≤1/(a*(a+1)*(a+2))
    have eqn : 1/(a+1)^3=(1-1/(a+1)^2)*(1/(a*(a+1)*(a+2))) := by field_simp [hp.ne',h1.ne',h2.ne']; ring
    rw [eqn]
    have ha : (N:ℝ)+1≤a+1 := by dsimp [a]; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) j]
    have hg := one_div_le_one_div_of_le (by positivity : 0<((N:ℝ)+1)^2) (pow_le_pow_left₀ (by positivity) ha 2)
    exact ⟨mul_le_mul_of_nonneg_right (by dsimp [k]; linarith) (by positivity),
      mul_le_of_le_one_left (by positivity) (by have := one_div_nonneg.mpr (sq_nonneg (a+1)); linarith)⟩
  have lo := ((h.mul_left k).summable.tsum_le_tsum (fun j => (bounds j).1) ht.summable)
  have hi := (ht.summable.tsum_le_tsum (fun j => (bounds j).2) h.summable)
  rw [(h.mul_left k).tsum_eq,ht.tsum_eq] at lo
  rw [ht.tsum_eq,h.tsum_eq] at hi
  constructor <;> linarith

theorem single_pole_decimal_bounds :
    0.901542676<singleConstant ∧ singleConstant<0.901542679 ∧
    0.0790756<singleConstant-k₀ ∧ singleConstant-k₀<0.0790757 ∧
    -0.1581513<2*k₀-2*singleConstant ∧ 2*k₀-2*singleConstant< -0.1581512 := by
  obtain ⟨hl,hu⟩ := zeta_tail_bounds (N:=128) (by decide)
  let S : ℚ := ∑ k ∈ range 129, 1/(k:ℚ)^3
  have h₁ : (0.901542676:ℚ)<3/4*(S+(1-1/(129:ℚ)^2)*(1/(2*128*129))) := by decide +kernel
  have h₂ : 3/4*(S+1/(2*128*129))<(0.901542679:ℚ) := by decide +kernel
  have q₁ := (Rat.cast_lt (K:=ℝ)).mpr h₁
  have q₂ := (Rat.cast_lt (K:=ℝ)).mpr h₂
  dsimp only [S] at q₁ q₂
  push_cast at q₁ q₂
  norm_num only [Nat.cast_ofNat,tailMajorant] at hl hu
  norm_num1 at q₁ q₂
  have lo : 0.901542676<singleConstant := by unfold singleConstant; linarith only [q₁,hl]
  have hi : singleConstant<0.901542679 := by unfold singleConstant; linarith only [q₂,hu]
  have hπ₀ := pow_lt_pow_left₀ Real.pi_gt_d20 (by norm_num) (by decide : 2≠0)
  have hπ₁ := pow_lt_pow_left₀ Real.pi_lt_d20 pi_pos.le (by decide : 2≠0)
  refine ⟨lo,hi,?_⟩; unfold k₀; constructor
  · linarith only [lo,hπ₁]
  · exact ⟨by linarith only [hi,hπ₀],by linarith only [hi,hπ₀],by linarith only [lo,hπ₁]⟩

end Liu
