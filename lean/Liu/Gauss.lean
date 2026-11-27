module

public import Liu.Pick
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter
open scoped BigOperators Topology
namespace Liu

def poch (a : ℝ) (n : ℕ) := (ascPochhammer ℝ n).eval a

theorem poch_pos {a : ℝ} (ha : 0 < a) (n : ℕ) : 0 < poch a n := by
  induction n with
  | zero => simp [poch,ascPochhammer_zero]
  | succ n ih =>
    unfold poch at ih ⊢
    rw [ascPochhammer_succ_right]
    simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_natCast]
    positivity

theorem Gamma_poch {a : ℝ} (ha : 0<a) (n : ℕ) : Gamma (a+n) = poch a n*Gamma a := by
  induction n with
  | zero => simp [poch,ascPochhammer_zero]
  | succ n ih =>
    have hp : 0 < a+n := by positivity
    rw [Nat.cast_succ,←add_assoc,Gamma_add_one hp.ne',ih]
    simp [poch,ascPochhammer_succ_right]
    ring

def betaWeight (a b x : ℝ) : ℝ := x^(a-1)*(1-x)^(b-1)

theorem betaWeight_integral {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    ∫ x in Ioo (0:ℝ) 1, betaWeight a b x = Gamma a * Gamma b / Gamma (a+b) := by
  have hh := Complex.betaIntegral_eq_Gamma_mul_div (a:ℂ) (b:ℂ) (by simpa) (by simpa)
  rw [Complex.betaIntegral,intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo,
    ←Complex.ofReal_add,Complex.Gamma_ofReal,Complex.Gamma_ofReal,Complex.Gamma_ofReal] at hh
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal,Complex.ofReal_div,Complex.ofReal_mul,←hh]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  simp only [betaWeight,Complex.ofReal_mul,Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le),Complex.ofReal_sub,Complex.ofReal_one]

theorem betaWeight_integrable {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    IntegrableOn (betaWeight a b) (Ioo (0:ℝ) 1) := by
  apply Integrable.of_integral_ne_zero
  rw [betaWeight_integral ha hb]
  exact (div_pos (mul_pos (Gamma_pos_of_pos ha) (Gamma_pos_of_pos hb))
    (Gamma_pos_of_pos (add_pos ha hb))).ne'

theorem binomial_pick_series (a : ℝ) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    HasSum (fun n : ℕ => (poch a n/(n.factorial:ℝ))*x^n) (1/(1-x)^a) := by
  have hab : |x| < 1 := by simpa [abs_of_pos hx.1] using hx.2
  have inside : x ∈ Metric.eball (0:ℝ) 1 := by
    rw [←ENNReal.ofReal_one,Metric.eball_ofReal]
    simpa [Real.dist_eq] using hab
  have hh := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum inside
  have coeff (n : ℕ) : Ring.choose (a+n-1) n = poch a n/(n.factorial:ℝ) := by
    rw [←Ring.multichoose_eq]
    apply (eq_div_iff (by positivity : (n.factorial:ℝ) ≠ 0)).mpr
    rw [mul_comm,←nsmul_eq_mul,Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
      Polynomial.ascPochhammer_smeval_eq_eval]
    rfl
  simpa [FormalMultilinearSeries.ofScalars_apply_eq,coeff,smul_eq_mul,mul_comm] using hh

/-- Positive real Gauss summation, the parameters needed near (τ,τ,2) in A.2.
The summation is derived from the beta integral and the binomial power series. -/
theorem gauss_sum_positive {a b c : ℝ} (ha : 0<a) (hb : 0<b) (hc : a+b<c) :
    HasSum (fun n : ℕ => poch a n * poch b n / ((n.factorial:ℝ)*poch c n))
      (Gamma c * Gamma (c-a-b)/(Gamma (c-a)*Gamma (c-b))) := by
  let μ := (volume:Measure ℝ).restrict (Ioo 0 1)
  let H := fun (n : ℕ) (x : ℝ) => poch a n/(n.factorial:ℝ)*x^n*betaWeight b (c-b) x
  let F := betaWeight b (c-a-b)
  have hcb : 0<c-b := by linarith
  have habc : 0<c-a-b := by linarith
  have hca : 0<c-a := by linarith
  have hc0 : 0<c := by linarith
  have hH (n : ℕ) (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : 0 ≤ H n x := by
    have hn := poch_pos ha n
    have h := sub_pos.mpr hx.2
    have hx0 := hx.1
    dsimp [H,betaWeight]; positivity
  have hseries (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : HasSum (fun n => H n x) (F x) := by
    have h := (binomial_pick_series a hx).mul_right (betaWeight b (c-b) x)
    have hd := sub_pos.mpr hx.2
    convert h using 1
    dsimp [F,betaWeight]
    rw [one_div,←rpow_neg hd.le,show c-a-b-1 = -a+(c-b-1) by ring,rpow_add hd]
    ring
  have moment (n : ℕ) : ∫ x, H n x ∂μ =
      (poch a n/(n.factorial:ℝ))*(Gamma (b+n)*Gamma (c-b)/Gamma (c+n)) := by
    have he : (fun x => H n x) =ᵐ[μ] (fun x => (poch a n/(n.factorial:ℝ))*betaWeight (b+n) (c-b) x) := by
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioo (a:=(0:ℝ)) (b:=1))] with x hx
      dsimp [H,betaWeight]
      rw [show b+(n:ℝ)-1=(n:ℝ)+(b-1) by ring,rpow_add hx.1,rpow_natCast]; ring
    rw [integral_congr_ae he,integral_const_mul]
    unfold μ
    rw [betaWeight_integral (by positivity) hcb,show b+(n:ℝ)+(c-b)=c+n by ring]
  have hfi : Integrable F μ := betaWeight_integrable hb habc
  have hm (n : ℕ) : Measurable (H n) := by dsimp [H,betaWeight]; fun_prop
  have hi (n : ℕ) : Integrable (H n) μ := by
    apply hfi.mono' (hm n).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioo (a:=(0:ℝ)) (b:=1))] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (hH n x hx)]
    simpa using sum_le_hasSum ({n}:Finset ℕ) (fun i _ => hH i x hx) (hseries x hx)
  have hlim : Tendsto (fun N : ℕ => ∫ x, ∑ n ∈ Finset.range N, H n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence F
    · intro N; exact (integrable_finsetSum _ (fun i _ => hi i)).aestronglyMeasurable
    · exact hfi
    · intro N
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioo (a:=(0:ℝ)) (b:=1))] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun i _ => hH i x hx))]
      exact sum_le_hasSum (Finset.range N) (fun i _ => hH i x hx) (hseries x hx)
    · filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioo (a:=(0:ℝ)) (b:=1))] with x hx
      exact (hseries x hx).tendsto_sum_nat
  simp_rw [integral_finsetSum _ (fun i _ => hi i)] at hlim
  let B := Gamma b * Gamma (c-b)/Gamma c
  have hB : 0 < B := div_pos (mul_pos (Gamma_pos_of_pos hb) (Gamma_pos_of_pos hcb)) (Gamma_pos_of_pos hc0)
  have he (n : ℕ) : (∫ x, H n x ∂μ)/B =
      poch a n*poch b n/((n.factorial:ℝ)*poch c n) := by
    rw [moment,Gamma_poch hb,Gamma_poch hc0]
    dsimp [B]
    field_simp [(Gamma_pos_of_pos hb).ne',(Gamma_pos_of_pos hcb).ne',(Gamma_pos_of_pos hc0).ne',
      (poch_pos hc0 n).ne'] <;> ring
  have hh := hlim.div_const B
  simp only [Finset.sum_div,he] at hh
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by
    have := poch_pos ha n; have := poch_pos hb n; have := poch_pos hc0 n; positivity) _).mpr
  convert hh using 2
  dsimp [μ,F,B]
  rw [betaWeight_integral hb habc,show b+(c-a-b)=c-a by ring]
  field_simp [(Gamma_pos_of_pos hb).ne',(Gamma_pos_of_pos hcb).ne',(Gamma_pos_of_pos hc0).ne',
    (Gamma_pos_of_pos hca).ne'] <;> ring

end Liu
