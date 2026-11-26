import Liu.GaussDerivatives

noncomputable section
open Set Filter Real Finset
open scoped Topology
namespace Liu

/-- The Gauss summand divided by Γ(c), so its logarithmic derivative in c
has the single factor −ψ(c+n). -/
def gaussWeight (a : ℝ) (n : ℕ) (c : ℝ) := (poch a n)^2/((n.factorial:ℝ)*Gamma (c+n))
def gaussValue (a c : ℝ) := Gamma (c-2*a)/(Gamma (c-a))^2

theorem gaussWeight_sum {a c : ℝ} (ha : 0<a) (hc : 2*a<c) :
    HasSum (fun n => gaussWeight a n c) (gaussValue a c) := by
  have hp : 0<c := by linarith
  have h := (gauss_sum_positive ha ha (c:=c) (by linarith)).div_const (Gamma c)
  have hval : Gamma c*Gamma (c-a-a)/(Gamma (c-a)*Gamma (c-a))/Gamma c=gaussValue a c := by
    dsimp [gaussValue]; rw [show c-a-a=c-2*a by ring,←sq]; field_simp [(Gamma_pos_of_pos hp).ne']
  rw [hval] at h
  apply h.congr_fun
  intro n; unfold gaussWeight
  rw [Gamma_poch hp]; ring

theorem gaussWeight_deriv {a c : ℝ} (hc : 0<c) (n : ℕ) :
    HasDerivAt (gaussWeight a n) (-psi (c+n)*gaussWeight a n c) c := by
  have hy : 0<c+n := by positivity
  have hd := (gamma_psi_derivative hy).comp c ((hasDerivAt_id c).add_const (n:ℝ))
  have hh := (((hd.const_mul (n.factorial:ℝ)).inv (mul_ne_zero (by positivity) (Gamma_pos_of_pos hy).ne'))).const_mul ((poch a n)^2)
  convert hh using 1
  · funext u; rfl
  · dsimp only [gaussWeight,id_eq,Function.comp_apply]
    field_simp [(Gamma_pos_of_pos hy).ne']

theorem gaussWeight_second {a c : ℝ} (hc : 0<c) (n : ℕ) :
    HasDerivAt (fun u => -psi (u+n)*gaussWeight a n u)
      ((psi (c+n)^2-trigamma (c+n))*gaussWeight a n c) c := by
  have hy : 0<c+n := by positivity
  have hp : HasDerivAt psi (trigamma (c+n)) (c+n) := (hasDerivAt_psi_series hy).differentiableAt.hasDerivAt
  have hh := ((hp.comp c ((hasDerivAt_id c).add_const (n:ℝ))).neg).mul (gaussWeight_deriv (a:=a) hc n)
  convert hh using 1
  · rfl
  · simp only [Pi.neg_apply,id_eq,Function.comp_apply,mul_one]; ring

private def reciprocalSum (c : ℝ) (n : ℕ) := ∑ j ∈ range n, (c+j)⁻¹

private theorem gamma_ratio_bound {c c₀ d : ℝ} (hc : 0<c₀) (hd : 0<d) (hgap : c₀+d≤c) (n : ℕ) :
    Gamma (c₀+n)*exp (d*reciprocalSum c n)/Gamma (c+n) ≤ Gamma c₀/Gamma c := by
  have hpc : 0<c := by linarith
  induction n with
  | zero => simp [reciprocalSum]
  | succ n h =>
    have hx : 0<c+n := by positivity
    have hy : 0<c₀+n := by positivity
    have hg := Real.add_one_le_exp (-(d/(c+n)))
    have hquot : (c₀+n)/(c+n)≤exp (-(d/(c+n))) := by
      apply le_trans _ hg
      apply (div_le_iff₀ hx).mpr
      field_simp [hx.ne']; linarith
    have hfac := mul_le_mul_of_nonneg_right hquot (exp_pos (d/(c+n))).le
    rw [←exp_add,neg_add_cancel,exp_zero] at hfac
    calc
      _ = (Gamma (c₀+n)*exp (d*reciprocalSum c n)/Gamma (c+n))*((c₀+n)/(c+n)*exp (d/(c+n))) := by
        rw [Nat.cast_succ,←add_assoc,←add_assoc,Gamma_add_one hx.ne',Gamma_add_one hy.ne']
        simp [reciprocalSum,sum_range_succ,mul_add,exp_add,div_eq_mul_inv]; ring
      _ ≤ _ := (mul_le_of_le_one_right (by positivity) hfac).trans h

private theorem trigamma_large_bound {x : ℝ} (hx : 1≤x) : 0≤trigamma x ∧ trigamma x≤π^2/6 := by
  rw [trigamma_eq_series (zero_lt_one.trans_le hx)]
  have h := hasSum_zeta_two
  rw [←hasSum_nat_add_iff' 1] at h
  have h' : HasSum (fun n : ℕ => 1/((n:ℝ)+1)^2) (π^2/6) := by simpa using h
  have hp (n : ℕ) : 1/(x+n)^2≤1/((n:ℝ)+1)^2 := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hs := Summable.of_nonneg_of_le (fun n => by positivity : ∀ n : ℕ, 0≤1/(x+n)^2) hp h'.summable
  exact ⟨tsum_nonneg (fun n => by positivity),(hs.tsum_le_tsum hp h'.summable).trans_eq h'.tsum_eq⟩

/-- A summable bound for two c derivatives on a fixed interval surrounding c=2.
The gap from 2a absorbs the square of the finite harmonic sum in ψ(c+n). -/
theorem gaussWeight_dominated {a : ℝ} (ha : a∈Set.Ioo 0 1) :
    ∃ l : ℝ, 2*a<l ∧ l<2 ∧ ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n : ℕ, ∀ c∈Set.Ioo l 3,
        |psi (c+n)*gaussWeight a n c|≤u n ∧
        |(psi (c+n)^2-trigamma (c+n))*gaussWeight a n c|≤u n := by
  let b := 1+a
  let d := (1-a)/2
  have hb : 2*a<b := by dsimp [b]; linarith [ha.2]
  have hb1 : 1<b := by dsimp [b]; linarith [ha.1]
  have hb0 := zero_lt_one.trans hb1
  have hd : 0<d := by dsimp [d]; linarith [ha.2]
  let l := b+d
  have hl : 2*a<l := by dsimp [l]; linarith
  have hl2 : l<2 := by dsimp [l,b,d]; linarith [ha.2]
  have hc₀ (c : ℝ) (hc : c∈Set.Icc l 3) : 0<c := by linarith [hc.1,ha.1]
  have hinv : ContinuousOn (fun c => (Gamma c)⁻¹) (Set.Icc l 3) := fun c hc =>
    ((differentiableAt_Gamma (fun n => ne_of_gt (by linarith [hc₀ c hc,Nat.cast_nonneg (α:=ℝ) n]))).inv (Gamma_pos_of_pos (hc₀ c hc)).ne').continuousAt.continuousWithinAt
  have hpsi : ContinuousOn psi (Set.Icc l 3) := fun c hc => (hasDerivAt_psi_series (hc₀ c hc)).continuousAt.continuousWithinAt
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hinv
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hpsi
  let M := Gamma b*|A|
  have hM : 0≤M := mul_nonneg (Gamma_pos_of_pos hb0).le (abs_nonneg _)
  let C := 1+2*B^2+4/d^2+π^2/6
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨l,hl,hl2,fun n => (C*M)*gaussWeight a n b,(gaussWeight_sum ha.1 hb).summable.mul_left _,?_⟩
  intro n c hc
  have hh : c∈Set.Icc l 3 := ⟨hc.1.le,hc.2.le⟩
  have hcp := hc₀ c hh
  have hG := Gamma_pos_of_pos (show 0<b+n by positivity)
  have hGc := Gamma_pos_of_pos (show 0<c+n by positivity)
  let W := gaussWeight a n c
  let S := reciprocalSum c n
  have hS : 0≤S := sum_nonneg (fun j _ => by positivity)
  have hW : 0≤W := div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) hGc.le)
  have eg := exp_pos (d*S)
  have eg1 := one_le_exp (mul_nonneg hd.le hS)
  have hratio := gamma_ratio_bound hb0 hd hc.1.le n
  have hA' : (Gamma c)⁻¹≤|A| := ((le_abs_self _).trans (hA c hh)).trans (le_abs_self _)
  have hdom : W*exp (d*S)≤M*gaussWeight a n b := by
    have hbase : exp (d*S)/Gamma (c+n)≤M/Gamma (b+n) := by
      apply (le_div_iff₀ hG).mpr
      calc
        _ = Gamma (b+n)*exp (d*S)/Gamma (c+n) := by ring
        _ ≤ Gamma b/Gamma c := hratio
        _ ≤ M := by dsimp only [M]; rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hA' (Gamma_pos_of_pos hb0).le
    calc
      _ = ((poch a n)^2/(n.factorial:ℝ))*(exp (d*S)/Gamma (c+n)) := by dsimp only [W,gaussWeight]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hbase (by positivity : 0≤(poch a n)^2/(n.factorial:ℝ))).trans_eq (by dsimp only [gaussWeight]; ring)
  have hS2 : S^2≤(2/d^2)*exp (d*S) := by
    have he := quadratic_le_exp_of_nonneg (mul_nonneg hd.le hS)
    rw [div_mul_eq_mul_div]; apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith only [he,mul_nonneg hd.le hS]
  have hpsi₂ : (psi (c+n))^2 ≤ (2*B^2+4/d^2)*exp (d*S) := by
    have hs : psi (c+n)=psi c+S := psi_add_nat hcp n
    have bb := pow_le_pow_left₀ (abs_nonneg _) (hB c hh) 2
    simp only [Real.norm_eq_abs,sq_abs] at bb
    rw [hs]
    calc
      _ ≤ 2*(psi c)^2+2*S^2 := by nlinarith only [sq_nonneg (psi c-S)]
      _ ≤ 2*(B^2*exp (d*S))+2*((2/d^2)*exp (d*S)) := add_le_add
        (mul_le_mul_of_nonneg_left (bb.trans (le_mul_of_one_le_right (sq_nonneg B) eg1)) (by norm_num))
        (mul_le_mul_of_nonneg_left hS2 (by norm_num))
      _ = _ := by ring
  have hg := trigamma_large_bound (x:=c+n) (by linarith [hc.1,show b+d=l from rfl,Nat.cast_nonneg (α:=ℝ) n])
  have bound₁ : |psi (c+n)|≤C*exp (d*S) := by
    have ht := sq_nonneg (|psi (c+n)|-1)
    dsimp only [C]
    nlinarith only [ht,sq_abs (psi (c+n)),hpsi₂,eg1,mul_nonneg (sq_nonneg π) eg.le,sq_nonneg (psi (c+n))]
  have bound₂ : |psi (c+n)^2-trigamma (c+n)|≤C*exp (d*S) := by
    apply (abs_sub ..).trans
    rw [abs_of_nonneg (sq_nonneg _),abs_of_nonneg hg.1]
    dsimp only [C]; nlinarith only [hpsi₂,hg.2,eg.le,mul_le_mul_of_nonneg_left eg1 (sq_nonneg π)]
  have both (v : ℝ) (hv : |v|≤C*exp (d*S)) : |v*W|≤C*M*gaussWeight a n b := by
    rw [abs_mul,abs_of_nonneg hW]
    calc
      _ ≤ (C*exp (d*S))*W := mul_le_mul_of_nonneg_right hv hW
      _ = C*(W*exp (d*S)) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hdom hC).trans_eq (by ring)
  exact ⟨both _ bound₁,both _ bound₂⟩

end Liu
