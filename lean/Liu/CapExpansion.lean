import Liu.CapWeights
import Liu.SinglePoleReduction

noncomputable section
open Real Set Filter Finset
open scoped Topology
namespace Liu

private def zetaThree := ∑' n : ℕ, 1/(n:ℝ)^3

private theorem zetaThree_nonneg : 0≤zetaThree := tsum_nonneg (fun n => by positivity)

theorem trigamma_one_expansion :
    ∃ C ≥ 0, ∀ t : ℝ, 0≤t → |trigamma (1+t)-(π^2/6-2*(∑' n : ℕ, 1/(n:ℝ)^3)*t)|≤C*t^2 := by
  have hs2 := hasSum_zeta_two
  rw [←hasSum_nat_add_iff' 1] at hs2
  have h₂ : HasSum (fun n : ℕ => 1/((n:ℝ)+1)^2) (π^2/6) := by simpa using hs2
  have hs3 := ((summable_one_div_nat_pow (p:=3)).mpr (by decide)).hasSum
  rw [←hasSum_nat_add_iff' 1] at hs3
  have h₃ : HasSum (fun n : ℕ => 1/((n:ℝ)+1)^3) zetaThree := by simpa [zetaThree] using hs3
  let V := fun n : ℕ => 1/((n:ℝ)+1)^4
  have hV : Summable V := by simpa [V] using (summable_nat_add_iff 1).mpr ((summable_one_div_nat_pow (p:=4)).mpr (by decide))
  have hV0 : 0≤∑' n, V n := tsum_nonneg (fun n => by dsimp [V]; positivity)
  refine ⟨3*∑' n, V n,by positivity,?_⟩
  intro t ht
  let g := fun n : ℕ => 1/(1+t+n)^2
  have hg : Summable g := Summable.of_nonneg_of_le (fun n => by dsimp [g]; positivity)
    (fun n => one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith : (n:ℝ)+1≤1+t+n) 2)) h₂.summable
  let E := fun n : ℕ => g n-(1/((n:ℝ)+1)^2-(2*t)*(1/((n:ℝ)+1)^3))
  have hsum : HasSum E (trigamma (1+t)-(π^2/6-2*t*zetaThree)) := by
    rw [trigamma_eq_series (by linarith)]; exact hg.hasSum.sub (h₂.sub (h₃.mul_left (2*t)))
  have hd (n : ℕ) : 0≤E n ∧ E n≤(3*t^2)*V n := by
    let a := (n:ℝ)+1
    have ha : 0<a := by dsimp [a]; positivity
    have hb : 0<a+t := by positivity
    have iden : E n=t^2*(3*a+2*t)/(a^3*(a+t)^2) := by
      dsimp only [E,g]; rw [show 1+t+(n:ℝ)=a+t by dsimp only [a]; ring]
      change 1/(a+t)^2-(1/a^2-(2*t)*(1/a^3))=_
      field_simp [ha.ne',hb.ne']; ring
    rw [iden]; refine ⟨by positivity,?_⟩
    change _ ≤ (3*t^2)*(1/a^4)
    rw [mul_one_div]; apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_nonneg (show 0≤t^2*a^3 by positivity) (show 0≤4*a*t+3*t^2 by positivity)]
  have hh := hsum.summable.tsum_le_tsum (fun n => (hd n).2) (hV.mul_left (3*t^2))
  rw [hsum.tsum_eq,tsum_mul_left] at hh
  have hz : 0≤∑' n, E n := tsum_nonneg (fun n => (hd n).1)
  rw [hsum.tsum_eq] at hz
  change |trigamma (1+t)-(π^2/6-2*zetaThree*t)|≤_
  rw [mul_right_comm 2 zetaThree t,abs_of_nonneg hz]
  linarith only [hh]

private def gammaRatio (t : ℝ) := (Gamma (1+t))^2/Gamma (1+2*t)

private theorem gammaRatio_bound :
    ∃ C ≥ 0, ∀ᶠ t in 𝓝[>] (0:ℝ), |gammaRatio t-1|≤C*t := by
  have hG : DifferentiableAt ℝ Gamma 1 := differentiableAt_Gamma (fun n => by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
  have hg : DifferentiableAt ℝ gammaRatio 0 := by
    have ht : DifferentiableAt ℝ (fun t : ℝ => Gamma (1+t)) 0 := by
      exact (show DifferentiableAt ℝ Gamma (1+(0:ℝ)) by simpa using hG).comp 0 (differentiableAt_id.const_add 1)
    have hu : DifferentiableAt ℝ (fun t : ℝ => Gamma (1+2*t)) 0 := by
      have hlin : DifferentiableAt ℝ (fun t : ℝ => 1+2*t) 0 := by fun_prop
      exact (show DifferentiableAt ℝ Real.Gamma (1+2*(0:ℝ)) by simpa using hG).comp (g:=Real.Gamma) (f:=fun t : ℝ => 1+2*t) 0 hlin
    exact (ht.pow 2).div hu (by simp)
  obtain ⟨C,hC,hh⟩ := hg.isBigO_sub.exists_pos
  refine ⟨C,hC.le,?_⟩
  have h := hh.bound.filter_mono (nhdsWithin_le_nhds (s:=Ioi 0))
  filter_upwards [h,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht ht0
  simpa [gammaRatio,Real.norm_eq_abs,abs_of_pos (show 0<t from ht0)] using ht

private theorem capSigma_normalized_expansion :
    ∃ C ≥ 0, ∀ᶠ t in 𝓝[>] (0:ℝ), |capSigma (1+t)/capNorm (1+t)-2*t*zetaThree|≤C*t^2 := by
  obtain ⟨A,hA,ha⟩ := capSigma_linear_bound
  obtain ⟨B,hB,hb⟩ := gammaRatio_bound
  have hZ := zetaThree_nonneg
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  refine ⟨2*(A*(1+B)+zetaThree*B),by positivity,?_⟩
  filter_upwards [hb,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),h0.eventually_lt_const zero_lt_one] with t hγ ht ht1
  change 0<t at ht
  have hσ := ha t ⟨ht.le,ht1.le⟩
  rw [capSigma_endpoint] at hσ
  change |capSigma (1+t)-zetaThree| ≤ A*t at hσ
  have hpos : 0<gammaRatio t := div_pos (sq_pos_of_pos (Gamma_pos_of_pos (by linarith))) (Gamma_pos_of_pos (by linarith))
  have hbound : |gammaRatio t|≤1+B := by
    rw [abs_of_pos hpos]; linarith [le_abs_self (gammaRatio t-1),mul_le_of_le_one_right hB ht1.le]
  have hf : capSigma (1+t)/capNorm (1+t) = 2*t*(capSigma (1+t)*gammaRatio t) := by
    dsimp [capNorm,gammaRatio]
    rw [show 2*(1+t)-2=2*t by ring,show 1+2*t=2*t+1 by ring,Gamma_add_one (by positivity : 2*t≠0)]
    field_simp [(Gamma_pos_of_pos (by linarith : 0<1+t)).ne',(Gamma_pos_of_pos (by positivity : 0<2*t)).ne']
  rw [hf,←mul_sub,abs_mul,abs_of_pos (by positivity : 0<2*t)]
  have he : capSigma (1+t)*gammaRatio t-zetaThree=(capSigma (1+t)-zetaThree)*gammaRatio t+zetaThree*(gammaRatio t-1) := by ring
  rw [he]
  apply (mul_le_mul_of_nonneg_left (abs_add_le ..) (by positivity : 0≤2*t)).trans
  rw [abs_mul,abs_mul,abs_of_nonneg hZ]
  apply (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul hσ hbound (abs_nonneg _) (by positivity)) (mul_le_mul_of_nonneg_left hγ hZ)) (by positivity : 0≤2*t)).trans_eq
  ring

/-- The special-function expression on the right of (cap-exact) has the
printed linear coefficient and a quadratic remainder. -/
theorem capExpression_expansion :
    ∃ C ≥ 0, ∀ᶠ t in 𝓝[>] (0:ℝ),
      |capExpression (1+t)-k₀-(2*k₀-2*singleConstant)*t|≤C*t^2 := by
  obtain ⟨A,hA,ha⟩ := trigamma_one_expansion
  obtain ⟨B,hB,hb⟩ := capSigma_normalized_expansion
  let a := π^2/6
  let z := zetaThree
  have hz : 0≤z := zetaThree_nonneg
  have hapos : 0≤a := by dsimp [a]; positivity
  have hk : k₀=a/2 := by dsimp [k₀,a]; ring
  have hc : singleConstant=3/4*z := rfl
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  refine ⟨2*A+B+(a/2+5*z),by positivity,?_⟩
  filter_upwards [hb,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),h0.eventually_lt_const zero_lt_one] with t hr ht ht1
  change 0<t at ht
  let T := trigamma (1+t)-(a-2*z*t)
  let N := capSigma (1+t)/capNorm (1+t)-2*t*z
  have hT : |T|≤A*t^2 := ha t ht.le
  have hN : |N|≤B*t^2 := hr
  have he : capExpression (1+t)-k₀-(2*k₀-2*singleConstant)*t =
      (1+t)^2/4*(2*T-N)+t^2*(a/2-3*z-3/2*z*t) := by
    rw [hk,hc]; dsimp [capExpression,T,N]; ring
  have hfac : (1+t)^2/4≤1 := by nlinarith [pow_le_pow_left₀ (by linarith : 0≤1+t) (by linarith : 1+t≤2) 2]
  have hdiff : |2*T-N|≤(2*A+B)*t^2 := by
    apply (abs_sub ..).trans
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith only [hT,hN]
  have hrest : |a/2-3*z-3/2*z*t|≤a/2+5*z := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hapos,hz,mul_nonneg hz ht.le,mul_le_of_le_one_right hz ht1.le]
  rw [he]
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤(1+t)^2/4),abs_of_nonneg (sq_nonneg t)]
  apply (add_le_add ((mul_le_of_le_one_left (abs_nonneg _) hfac).trans hdiff)
    (mul_le_mul_of_nonneg_left hrest (sq_nonneg t))).trans_eq
  ring

theorem cap_slope_of_exact_quotient
    (h : ∀ᶠ t in 𝓝[>] (0:ℝ), quotient (capPower (1+t))=capExpression (1+t)) :
    Tendsto (fun t : ℝ => (quotient (capPower (1+t))-k₀)/t) (𝓝[>] 0) (𝓝 (2*k₀-2*singleConstant)) := by
  obtain ⟨C,hC,hb⟩ := capExpression_expansion
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by simpa using h0.const_mul C)
  filter_upwards [hb,h,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht he hp
  change 0<t at hp
  rw [he,Real.norm_eq_abs,show (capExpression (1+t)-k₀)/t-(2*k₀-2*singleConstant) =
      (capExpression (1+t)-k₀-(2*k₀-2*singleConstant)*t)/t by field_simp,
      abs_div,abs_of_pos hp]
  exact ((div_le_iff₀ hp).mpr (ht.trans_eq (by ring)))

theorem coincidentDeficit_of_exact_cap_quotient
    (h : ∀ᶠ t in 𝓝[>] (0:ℝ), quotient (capPower (1+t))=capExpression (1+t)) : coincidentDeficit :=
  coincidentDeficit_iff_cap_slope.mpr (cap_slope_of_exact_quotient h)

end Liu
