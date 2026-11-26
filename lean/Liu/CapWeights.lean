import Liu.TrigammaSeries
import Liu.EulerSum

noncomputable section
open Real Set Filter Finset
open scoped Topology
namespace Liu

def capCoeff (τ : ℝ) (n : ℕ) := poch τ n/(n.factorial:ℝ)
def capSigma (α : ℝ) := ∑' n : ℕ, (capCoeff (2-α) n)^2 * (trigamma (n+2)/((n:ℝ)+1))
def capNorm (α : ℝ) := Gamma (2*α-2)/(Gamma α)^2
def capExpression (α : ℝ) := α^2/4*(2*trigamma α-capSigma α/capNorm α)

theorem capCoeff_succ (τ : ℝ) (n : ℕ) :
    capCoeff τ (n+1)=capCoeff τ n*((τ+n)/((n:ℝ)+1)) := by
  simp [capCoeff,poch,Nat.factorial_succ,ascPochhammer_succ_right]; field_simp

theorem capCoeff_endpoint_bound {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (n : ℕ) :
    0≤capCoeff (1-t) n ∧ capCoeff (1-t) n≤1 ∧ 1-capCoeff (1-t) n ≤ t*∑ j ∈ range n, 1/((j:ℝ)+1) := by
  induction n with
  | zero => simp [capCoeff,poch]
  | succ n ih =>
    let c := capCoeff (1-t) n
    let d := t/((n:ℝ)+1)
    have hd : 0≤d := div_nonneg ht.1 (by positivity)
    have hd1 : d≤1 := (div_le_self ht.1 (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)).trans ht.2
    have he : (1-t+n)/((n:ℝ)+1)=1-d := by dsimp [d]; field_simp; ring
    rw [capCoeff_succ,he,sum_range_succ,mul_add]
    change 0≤c*(1-d) ∧ c*(1-d)≤1 ∧ 1-c*(1-d)≤_+_
    refine ⟨mul_nonneg ih.1 (sub_nonneg.mpr hd1), (mul_le_of_le_one_right ih.1 (by linarith)).trans ih.2.1,?_⟩
    have hc : c*d≤d := mul_le_of_le_one_left hd ih.2.1
    change 1-c*(1-d)≤ _+t*(1/((n:ℝ)+1))
    rw [mul_one_div]; linarith [ih.2.2]

theorem trigamma_integer_tail (n : ℕ) :
    trigamma (n+2)=∑' j : ℕ, 1/((n:ℝ)+j+2)^2 := by
  rw [trigamma_eq_series (by positivity)]
  congr 1; funext j; congr 2; ring

theorem capSigma_endpoint : capSigma 1=∑' n : ℕ, 1/(n:ℝ)^3 := by
  rw [←euler_trigamma_tail]
  apply tsum_congr
  intro n
  have hc := capCoeff_endpoint_bound (t:=0) ⟨le_rfl,zero_le_one⟩ n
  have he : capCoeff (2-1) n=1 := by norm_num at hc ⊢; linarith [hc.2.1,hc.2.2]
  rw [he,trigamma_integer_tail]; ring

/-- The linear error in the coefficient series near the cap endpoint is summably
dominated, including the variation of all binomial coefficients. -/
theorem capSigma_linear_bound :
    ∃ C ≥ 0, ∀ t ∈ Icc (0:ℝ) 1, |capSigma (1+t)-capSigma 1| ≤ C*t := by
  let H := fun n : ℕ => ∑ j ∈ range n, 1/((j:ℝ)+1)
  let W := fun n : ℕ => trigamma (n+2)/((n:ℝ)+1)
  have hW (n : ℕ) : 0≤W n := by dsimp [W]; rw [trigamma_integer_tail]; exact div_nonneg (tsum_nonneg fun j => by positivity) (by positivity)
  have hWb (n : ℕ) : W n≤1/((n:ℝ)+1)^2 := by
    dsimp [W]; rw [trigamma_integer_tail]
    apply (div_le_div_of_nonneg_right (reciprocal_square_tail n) (by positivity : 0≤(n:ℝ)+1)).trans_eq
    rw [div_div,←sq]
  have hS : Summable W := Summable.of_nonneg_of_le hW hWb (by
    simpa using (summable_nat_add_iff 1).mpr ((summable_one_div_nat_pow (p:=2)).mpr (by decide)))
  have H0 (n : ℕ) : 0≤H n := sum_nonneg (fun _ _ => by positivity)
  let V := fun n : ℕ => H n/((n:ℝ)+1)^2
  have hV : Summable V := euler_harmonic_summable
  have V0 (n : ℕ) : 0≤V n := div_nonneg (H0 n) (sq_nonneg _)
  have hC : 0≤∑' n, V n := tsum_nonneg V0
  refine ⟨2*∑' n, V n,by positivity,?_⟩
  intro t ht
  let c := capCoeff (1-t)
  have hc := capCoeff_endpoint_bound ht
  have hc1 (n : ℕ) : c n^2≤1 := pow_le_one₀ (hc n).1 (hc n).2.1
  have A : Summable (fun n => c n^2*W n) := Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (hW n))
    (fun n => mul_le_of_le_one_left (hW n) (hc1 n)) hS
  have E : capSigma 1=∑' n, W n := by
    rw [capSigma_endpoint,←euler_trigamma_tail]
    apply tsum_congr; intro n; dsimp only [W]; rw [trigamma_integer_tail]; ring
  rw [E]
  change |(∑' n, capCoeff (2-(1+t)) n ^2*W n)-(∑' n, W n)| ≤ _
  rw [show 2-(1+t)=1-t by ring,abs_sub_comm]
  rw [←hS.tsum_sub A]
  have hp (n : ℕ) : 0≤W n-c n^2*W n := sub_nonneg.mpr (mul_le_of_le_one_left (hW n) (hc1 n))
  rw [abs_of_nonneg (tsum_nonneg hp)]
  have hb (n : ℕ) : W n-c n^2*W n ≤ (2*t)*V n := by
    have hv := mul_le_mul (hc n).2.2 (show 1+c n≤2 by linarith [(hc n).2.1]) (by linarith [(hc n).1]) (mul_nonneg ht.1 (H0 n))
    have hsq : 1-c n^2≤2*t*H n := by nlinarith only [hv]
    have hh := mul_le_mul hsq (hWb n) (hW n) (mul_nonneg (mul_nonneg (by norm_num) ht.1) (H0 n))
    dsimp only [V]; linarith only [show W n-c n^2*W n=(1-c n^2)*W n by ring,
      show (2*t*H n)*(1/((n:ℝ)+1)^2)=2*t*(H n/((n:ℝ)+1)^2) by ring,hh]
  exact ((hS.sub A).tsum_le_tsum hb (hV.mul_left (2*t))).trans_eq (by rw [tsum_mul_left]; ring)

end Liu
