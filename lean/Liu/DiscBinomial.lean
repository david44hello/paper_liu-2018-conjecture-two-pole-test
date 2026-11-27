module

public import Liu.DiscPowerL2

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter Finset Metric
open scoped Topology ComplexConjugate
namespace Liu

def discPower (τ : ℝ) (z : ℂ) := 1/(1-z)^(τ:ℂ)

theorem discPower_series (τ : ℝ) {z : ℂ} (hz : z∈disc) :
    HasSum (fun n => (capCoeff τ n:ℂ)*z^n) (discPower τ z) := by
  have inside : z∈Metric.eball (0:ℂ) 1 := by
    rw [←ENNReal.ofReal_one,Metric.eball_ofReal]; exact hz
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (τ:ℂ)).hasSum inside
  have hc (n : ℕ) : Ring.choose (τ+n-1) n=capCoeff τ n := by
    rw [←Ring.multichoose_eq,capCoeff]
    apply (eq_div_iff (by positivity : (n.factorial:ℝ)≠0)).mpr
    rw [mul_comm,←nsmul_eq_mul,Ring.factorial_nsmul_multichoose_eq_ascPochhammer,Polynomial.ascPochhammer_smeval_eq_eval]; rfl
  have cc (n : ℕ) : Ring.choose ((τ:ℂ)+n-1) n=(capCoeff τ n:ℂ) := by
    rw [←hc,show (τ:ℂ)+n-1 = Complex.ofRealHom (τ+n-1) by simp,←Ring.map_choose]; rfl
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,cc,zero_add,smul_eq_mul,mul_comm,discPower] using h

private theorem poch_two (n : ℕ) : poch 2 n=((n+1).factorial:ℝ) := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
    change (ascPochhammer ℝ (n+1)).eval 2=_
    rw [ascPochhammer_succ_right]
    simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_natCast]
    change poch 2 n*(2+n)=_
    rw [ih,Nat.factorial_succ (n+1)]; push_cast; ring

theorem capCoeff_gauss {a b : ℝ} (ha : 0<a) (hb : 0<b) (hab : a+b<2) :
    HasSum (fun n : ℕ => capCoeff a n*capCoeff b n/((n:ℝ)+1))
      (Gamma (2-a-b)/(Gamma (2-a)*Gamma (2-b))) := by
  have h := gauss_sum_positive ha hb (c:=2) hab
  have hG : Gamma 2=1 := by simpa using Gamma_nat_eq_factorial 1
  rw [hG,one_mul] at h
  apply h.congr_fun
  intro n
  rw [poch_two,Nat.factorial_succ]
  dsimp [capCoeff]; push_cast; field_simp

theorem capCoeff_square_summable {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    Summable (fun n : ℕ => ‖(capCoeff a n:ℂ)‖^2/((n:ℝ)+1)) := by
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simpa only [sq] using (capCoeff_gauss ha ha (by linarith)).summable

theorem discPower_memLp {a : ℝ} (ha : 0<a) (ha1 : a<1) : MemLp (discPower a) 2 discArea :=
  (disc_series_L2 (capCoeff_square_summable ha ha1) (fun _ hz => discPower_series a hz)).choose

/-- The two-parameter disc integral on the open square containing the
parameters differentiated in Lemma A.2. -/
theorem discPower_pairing {a b : ℝ} (ha : 0<a) (ha1 : a<1) (hb : 0<b) (hb1 : b<1) :
    (∫ z in disc, discPower a z*conj (discPower b z) ∂area) =
      ((Gamma (2-a-b)/(Gamma (2-a)*Gamma (2-b)):ℝ):ℂ) := by
  have hi := disc_series_pairing (capCoeff_square_summable hb hb1) (capCoeff_square_summable ha ha1)
    (fun _ hz => discPower_series b hz) (fun _ hz => discPower_series a hz)
  have hg := Complex.hasSum_ofReal.mpr (capCoeff_gauss ha hb (by linarith))
  apply hi.unique
  convert hg using 1
  funext n; push_cast; simp [mul_comm]

theorem discPower_energy {α : ℝ} (ha : 1<α) (hb : α<2) :
    (∫ z in disc, ‖discPower (2-α) z‖^2 ∂area)=capNorm α := by
  have h := discPower_pairing (a:=2-α) (b:=2-α) (by linarith) (by linarith) (by linarith) (by linarith)
  simp only [Complex.mul_conj',←Complex.ofReal_pow,integral_complex_ofReal,Complex.ofReal_inj] at h
  rw [show 2-(2-α)-(2-α)=2*α-2 by ring,show 2-(2-α)=α by ring,←sq] at h
  exact h

end Liu
