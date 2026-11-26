import Liu.PrefixTraceBounds
import Liu.IsolatedMoment

noncomputable section
open Set Real MeasureTheory
namespace Liu

def cutTrace (c d x : ℝ) := poissonLine c 1 x*isolatedTrace c d x

theorem cutTrace_integral_bound {u d : ℝ} (hu : 0<u) (hud : u≤d) (hu₁ : u≤1) (c : ℝ) :
    Integrable (cutTrace c d) ∧ (∫ x, cutTrace c d x)/π≤1+log (1/u) := by
  have hd := hu.trans_le hud
  refine ⟨(isolatedTrace_poisson_moment c hd).1,(isolatedTrace_log_moment c hd).2.trans ?_⟩
  have hd_inv := inv_anti₀ hu hud
  have he : 1+u⁻¹=(1+u)*(1/u) := by field_simp [hu.ne'] <;> ring
  have hlog := log_le_sub_one_of_pos (show 0<1+u by positivity)
  calc
    log (1+d⁻¹) ≤ log (1+u⁻¹) := log_le_log (by positivity) (by linarith)
    _ = log (1+u)+log (1/u) := by rw [he,log_mul (by positivity) (by positivity)]
    _ ≤ _ := by linarith

private theorem trace_tail {c d x : ℝ} (hc : |c|≤1) (hd : 0<d) (hx : 2 < |x|) :
    isolatedTrace c d x ≤ 4/|x| := by
  have htri := abs_sub_le x c 0
  simp only [sub_zero] at htri
  have hdist : |x|/2≤|x-c| := by linarith
  have hx₀ : 0 < |x| := by linarith
  have hd₀ := (half_pos hx₀).trans_le hdist
  apply (isolatedTrace_le_distance c x hd (sub_ne_zero.mp (abs_pos.mp hd₀))).trans
  apply (div_le_div_iff₀ (by positivity) hx₀).mpr
  nlinarith only [mul_le_mul_of_nonneg_right pi_lt_four.le hx₀.le,hdist]

/-- Finite-mass Poisson cutoffs dominate both isolated traces in the central
interval. Away from it the product decays like the unit Poisson kernel. -/
theorem prefix_product_envelope {s γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0<u)
    {C v : ℝ} (hC : 0≤C) (hv : |v|≤5*C) (x : ℝ) :
    let a := normalMass s
    let b := 1-a
    let d := sin γ+u
    let A := a*isolatedTrace 0 u x
    let B := b*isolatedTrace (cos γ) d x
    2*A*B+2*(A+B)*|v| ≤ (160+100*C)*(a*cutTrace 0 u x+b*cutTrace (cos γ) d x)
      +100*poissonLine 0 1 x+8*|v| := by
  let a := normalMass s
  let b := 1-a
  let c := cos γ
  let d := sin γ+u
  let A := a*isolatedTrace 0 u x
  let B := b*isolatedTrace c d x
  let P := poissonLine 0 1 x
  let Q := poissonLine c 1 x
  have ha : 0<a := Certificate.normalMass_pos _
  have hb : 0<b := by dsimp [b,a]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _
  have hab : a+b=1 := by dsimp [b]; ring
  have hd : 0<d := add_pos_of_nonneg_of_pos (sin_nonneg_of_nonneg_of_le_pi hg.1 (hg.2.trans (by linarith [pi_pos]))) hu
  have hA : 0≤A := mul_nonneg ha.le (isolatedTrace_nonneg _ _ hu)
  have hB : 0≤B := mul_nonneg hb.le (isolatedTrace_nonneg _ _ hd)
  have hP : 0≤P := by dsimp [P,poissonLine]; positivity
  have hQ : 0≤Q := by dsimp [Q,poissonLine]; positivity
  have hsum : 0≤P*A+Q*B := by positivity
  have e : a*cutTrace 0 u x+b*cutTrace c d x=P*A+Q*B := by dsimp [A,B,P,Q,cutTrace]; ring
  change 2*A*B+2*(A+B)*|v|≤(160+100*C)*(a*cutTrace 0 u x+b*cutTrace c d x)+100*P+8*|v|
  rw [e]
  by_cases hx : |x|≤2
  · have lower (y : ℝ) (hy : |y|≤1) : 1≤10*poissonLine y 1 x := by
      have hn := abs_sub x y
      have h3 : |x-y|≤3 := by linarith
      have hpow := pow_le_pow_left₀ (abs_nonneg _) h3 2
      rw [sq_abs] at hpow
      unfold poissonLine
      rw [mul_one_div,le_div_iff₀ (by positivity)]
      nlinarith
    have hcut : A+B≤10*(P*A+Q*B) := by
      nlinarith only [mul_le_mul_of_nonneg_right (lower 0 (by norm_num)) hA,
        mul_le_mul_of_nonneg_right (lower c (abs_cos_le_one _)) hB]
    have hc : 2*A*B≤16*(A+B) := by
      rcases isolated_min_bound (s:=s) hg hu x with h|h
      · change A≤8 at h
        nlinarith only [mul_le_mul_of_nonneg_right h hB,hA]
      · change B≤8 at h
        nlinarith only [mul_le_mul_of_nonneg_left h hA,hB]
    nlinarith only [hc,hcut,mul_le_mul_of_nonneg_right hcut hC,
      mul_le_mul_of_nonneg_left hv (add_nonneg hA hB),hP,abs_nonneg v]
  · have hX := lt_of_not_ge hx
    have hx₀ : 0 < |x| := by linarith
    have hi := trace_tail (c:=0) (by norm_num) hu hX
    have hj := trace_tail (c:=c) (abs_cos_le_one _) hd hX
    have hA' : A≤a*(4/|x|) := mul_le_mul_of_nonneg_left hi ha.le
    have hB' : B≤b*(4/|x|) := mul_le_mul_of_nonneg_left hj hb.le
    have hAB' : A+B≤4/|x| := by nlinarith only [hA',hB',congrArg (fun w : ℝ => w*(4/|x|)) hab]
    have hAB : A+B≤4 := hAB'.trans ((div_le_iff₀ hx₀).mpr (by linarith))
    have hK : 2*A*B≤100*P := by
      have ha₁ : A≤4/|x| := by linarith
      have hb₁ : B≤4/|x| := by linarith
      have hmul := mul_le_mul ha₁ hb₁ hB (by positivity : 0≤4/|x|)
      apply (show 2*A*B≤2*((4/|x|)*(4/|x|)) by nlinarith only [hmul]).trans
      change 2*(4/|x| *(4/|x|))≤100*(1/((x-0)^2+1^2))
      rw [div_mul_div_comm,←sq |x|,sq_abs,sub_zero,one_pow,mul_one_div,←mul_div_assoc]
      apply (div_le_div_iff₀ (by simpa only [sq_abs] using sq_pos_of_pos hx₀) (by positivity)).mpr
      nlinarith [show 4≤x^2 by rw [←sq_abs]; nlinarith [sq_nonneg (|x|-2)]]
    nlinarith only [hK,mul_le_mul_of_nonneg_right hAB (abs_nonneg v),hsum,mul_nonneg hC hsum]

end Liu
