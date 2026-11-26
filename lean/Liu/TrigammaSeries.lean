import Liu.Gauss
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

noncomputable section
open Set Real Filter Finset
open scoped Topology
namespace Liu

/-- The printed real functions ψ and ψ₁ on the positive axis. -/
def psi (x : ℝ) := deriv (Real.log ∘ Real.Gamma) x
def trigamma (x : ℝ) := deriv psi x

private theorem logGamma_diff {x : ℝ} (hx : 0<x) : DifferentiableAt ℝ (Real.log ∘ Real.Gamma) x :=
  (differentiableAt_Gamma (fun n => by have := Nat.cast_nonneg (α:=ℝ) n; linarith)).log (Gamma_pos_of_pos hx).ne'

theorem psi_eq_gamma_ratio {x : ℝ} (hx : 0<x) : psi x=deriv Real.Gamma x/Real.Gamma x := by
  rw [psi,Function.comp_def,deriv.log (differentiableAt_Gamma (fun n => by have := Nat.cast_nonneg (α:=ℝ) n; linarith)) (Gamma_pos_of_pos hx).ne']

theorem psi_add_one {x : ℝ} (hx : 0<x) : psi (x+1)=psi x+x⁻¹ := by
  let f := Real.log ∘ Real.Gamma
  change deriv f (x+1)=deriv f x+x⁻¹
  rw [←deriv_comp_add_const,←deriv_log,←deriv_add (logGamma_diff hx) (differentiableAt_log hx.ne')]
  apply EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] with y hy
  simp [f,Gamma_add_one hy.ne',Real.log_mul hy.ne' (Gamma_pos_of_pos hy).ne',add_comm]

theorem psi_add_nat {x : ℝ} (hx : 0<x) (n : ℕ) :
    psi (x+n)=psi x+∑ k ∈ range n, (x+k)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ,←add_assoc,psi_add_one (by positivity),ih,sum_range_succ]; ring

private theorem psi_monotone : MonotoneOn psi (Ioi 0) :=
  convexOn_log_Gamma.monotoneOn_deriv (fun _ hx => logGamma_diff hx)

private theorem psi_shift_difference {x : ℝ} (hx : 0<x) :
    Tendsto (fun n : ℕ => psi (x+n)-psi (1+n)) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max x 1)
  have hNx := (le_max_left ..).trans hN.le
  have hN1 := (le_max_right ..).trans hN.le
  have hinv : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero_norm' (a:=fun n : ℕ => (N:ℝ)*(n:ℝ)⁻¹) _ (by simpa using hinv.const_mul (N:ℝ))
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hnr : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have lo (y : ℝ) (hy : 0<y) : psi n≤psi (y+n) :=
    psi_monotone hnr (show 0<y+n by positivity) (by linarith)
  have hi (y : ℝ) (hy : 0<y) (hyN : y≤N) : psi (y+n)≤psi ((n:ℝ)+N) :=
    psi_monotone (show 0<y+n by positivity) (show 0<(n:ℝ)+N by positivity) (by linarith)
  have hb : psi ((n:ℝ)+N)-psi n ≤ (N:ℝ)*(n:ℝ)⁻¹ := by
    rw [psi_add_nat hnr,add_sub_cancel_left]
    apply (sum_le_sum (s:=range N) (g:=fun _ => (n:ℝ)⁻¹) (fun k _ => inv_anti₀ hnr (by have := Nat.cast_nonneg (α:=ℝ) k; linarith))).trans_eq
    simp
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [lo x hx,hi 1 zero_lt_one hN1],by linarith [hi x hx hNx,lo 1 zero_lt_one]⟩

private theorem inverse_sum_bound {x : ℝ} (hx : 0<x) (n : ℕ) :
    (x+n)⁻¹ ≤ (min 1 x)⁻¹*((n:ℝ)+1)⁻¹ := by
  have hc : 0 < min 1 x := lt_min zero_lt_one hx
  rw [←mul_inv]
  apply inv_anti₀ (by positivity)
  nlinarith only [min_le_right 1 x,mul_le_mul_of_nonneg_right (min_le_left 1 x) (Nat.cast_nonneg n : (0:ℝ)≤n)]

private def psiTerm (n : ℕ) (x : ℝ) := (1+(n:ℝ))⁻¹-(x+n)⁻¹

private theorem shifted_square_sum : Summable (fun n : ℕ => (((n:ℝ)+1)⁻¹)^2) := by
  simpa [one_div] using (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p:=2)).mpr (by decide))

private theorem psiTerm_summable {x : ℝ} (hx : 0<x) : Summable (fun n => psiTerm n x) := by
  let C := |x-1| *(min 1 x)⁻¹
  have hs := shifted_square_sum.mul_left C
  apply Summable.of_norm_bounded hs
  intro n
  have h1 : 0<1+(n:ℝ) := by positivity
  have h2 : 0<x+n := by positivity
  have he : psiTerm n x=(x-1)*((n:ℝ)+1)⁻¹*(x+n)⁻¹ := by unfold psiTerm; field_simp; ring
  rw [he,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr h2.le),abs_of_nonneg (by positivity : 0≤((n:ℝ)+1)⁻¹)]
  apply (mul_le_mul_of_nonneg_left (inverse_sum_bound hx n) (by positivity : 0≤|x-1| *((n:ℝ)+1)⁻¹)).trans_eq
  dsimp only [C]; ring

theorem psi_series {x : ℝ} (hx : 0<x) :
    psi x=psi 1+∑' n : ℕ, ((1+(n:ℝ))⁻¹-(x+n)⁻¹) := by
  have he (n : ℕ) : psi (x+n)-psi (1+n)=(psi x-psi 1)-∑ k ∈ range n, psiTerm k x := by
    rw [psi_add_nat hx,psi_add_nat zero_lt_one]; simp only [psiTerm,sum_sub_distrib]; ring
  have h := (psi_shift_difference hx)
  simp_rw [he] at h
  have h' := (psiTerm_summable hx).hasSum.tendsto_sum_nat.const_sub (psi x-psi 1)
  have eqn := tendsto_nhds_unique h h'
  dsimp only [psiTerm] at eqn; linarith

theorem hasDerivAt_psi_series {x : ℝ} (hx : 0<x) :
    HasDerivAt psi (∑' n : ℕ, 1/(x+n)^2) x := by
  let c := min 1 (x/2)
  have hc : 0<c := lt_min zero_lt_one (half_pos hx)
  let D := Ioi (x/2)
  have hxD : x∈D := by change x/2<x; linarith
  let u := fun n : ℕ => (c⁻¹)^2*(((n:ℝ)+1)⁻¹)^2
  have hu : Summable u := shifted_square_sum.mul_left _
  have hd (n : ℕ) (y : ℝ) (hy : y∈D) : HasDerivAt (psiTerm n) (1/(y+n)^2) y := by
    have hyp : 0<y := (half_pos hx).trans hy
    have h := (((hasDerivAt_id y).add_const (n:ℝ)).inv (by dsimp; positivity)).const_sub (1+(n:ℝ))⁻¹
    convert h using 1
    · rfl
    · dsimp; ring
  have hb (n : ℕ) (y : ℝ) (hy : y∈D) : ‖1/(y+n)^2‖≤u n := by
    have hyp : 0<y := (half_pos hx).trans hy
    have hh := (inv_anti₀ (show 0<x/2+n by positivity) (by change x/2+n≤y+n; linarith [show x/2<y from hy])).trans (inverse_sum_bound (half_pos hx) n)
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤1/(y+n)^2),one_div,←inv_pow]
    exact (pow_le_pow_left₀ (by positivity) hh 2).trans_eq (mul_pow ..)
  have h := hasDerivAt_tsum_of_isPreconnected (t:=D) hu isOpen_Ioi (convex_Ioi _).isPreconnected
    hd hb hxD (psiTerm_summable hx) hxD
  apply (h.const_add (psi 1)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy using psi_series hy

theorem trigamma_eq_series {x : ℝ} (hx : 0<x) : trigamma x=∑' n : ℕ, 1/(x+n)^2 :=
  (hasDerivAt_psi_series hx).deriv

end Liu
