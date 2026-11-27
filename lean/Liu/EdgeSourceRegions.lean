module

public import Liu.CrossClaim

@[expose] public section

noncomputable section
open Set Real
namespace Liu

/-- Fixed positive angle estimates for the actual real and complex cross
source used in Appendix E.3(b). -/
theorem edge_source_fixed_angle {s γ : ℝ} (hg : γ∈Icc 0 (π/2)) (hσ : 0<sin γ)
    {z : ℂ} (hz : 0<z.im) :
    let a := normalMass s
    let b := 1-a
    let H := crossSource a (direction γ) z
    |H.re|≤2*b/(a*sin γ^4) ∧ ‖H‖≤2*b/(‖z‖*sin γ^3) ∧
      (2≤‖z‖ → ‖H‖≤4/‖z‖^4) := by
  let a := normalMass s
  let b := 1-a
  let σ := sin γ
  let q := direction γ
  let r := ‖z‖
  let t := ‖z-q‖
  let v := ‖z-(a:ℂ)*q‖
  let Y := z.re*σ+z.im*cos γ
  have ha : 0<a := Certificate.normalMass_pos s
  have hb : 0<b := by dsimp [a,b]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _
  have hr : 0<r := norm_pos_iff.mpr (fun e => by simp [e] at hz)
  have ht : σ≤t := by apply le_trans _ (Complex.im_le_norm _); simp [q,Complex.sub_im,direction_im,σ]; linarith
  have hv : a*σ≤v := by apply le_trans _ (Complex.im_le_norm _); simp [Complex.sub_im,Complex.mul_im,q,direction_im,σ]; linarith
  have ht' := hσ.trans_le ht
  have hv' := (mul_pos ha hσ).trans_le hv
  obtain ⟨_,hreal,hneg,habs,hY⟩ := cross_source_claim s γ hg hz
  change _= -2*a*b*Y^2/(r^2*t^2*v^2) at hreal
  change _=2*a*b*|Y|/(r^2*t^2*v) at habs
  change |Y|≤ min r (min t v) at hY
  have hYr := hY.trans (min_le_left ..)
  have hYv := hY.trans ((min_le_right ..).trans (min_le_right ..))
  dsimp only
  rw [abs_of_nonpos hneg,hreal,habs]
  change -(-2*a*b*Y^2/(r^2*t^2*v^2))≤2*b/(a*σ^4) ∧ _ 
  have hd₁ : σ^2*(a*σ)^2≤t^2*v^2 :=
    mul_le_mul (pow_le_pow_left₀ hσ.le ht 2) (pow_le_pow_left₀ (mul_pos ha hσ).le hv 2) (sq_nonneg _) (sq_nonneg _)
  have hd₂ : σ^2*(a*σ)≤t^2*v := mul_le_mul (pow_le_pow_left₀ hσ.le ht 2) hv (mul_pos ha hσ).le (sq_nonneg _)
  refine ⟨?_,?_,?_⟩
  · have hy := pow_le_pow_left₀ (abs_nonneg _) hYr 2; rw [sq_abs] at hy
    apply (le_div_iff₀ (by positivity)).mpr
    field_simp [hr.ne',ht'.ne',hv'.ne']
    nlinarith only [mul_le_mul_of_nonneg_left hd₁ (sq_nonneg r),
      mul_le_mul_of_nonneg_left hy (by positivity : 0≤a^2*σ^4)]
  · change 2*a*b*|Y|/(r^2*t^2*v) ≤ 2*b/(r*σ^3)
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hd₂ (by positivity : 0≤b*r^2),
      mul_le_mul_of_nonneg_left hYr (by positivity : 0≤a*b*r*σ^3)]
  · intro hfar
    have hq : ‖q‖=1 := direction_norm _
    have hh := norm_sub_le_norm_sub_add_norm_sub z q 0
    have hh' := norm_sub_le_norm_sub_add_norm_sub z ((a:ℂ)*q) 0
    simp only [sub_zero,hq,norm_mul,Complex.norm_of_nonneg ha.le,mul_one] at hh hh'
    have ht₀ : r/2≤t := by change r≤t+1 at hh; linarith
    change 2*a*b*|Y|/(r^2*t^2*v)≤4/r^4
    have hy := mul_le_mul_of_nonneg_left hYv (by positivity : 0≤2*a*b)
    apply (div_le_div_of_nonneg_right hy (by positivity : 0≤r^2*t^2*v)).trans
    rw [mul_div_mul_right _ _ hv'.ne']
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have h₀ := pow_le_pow_left₀ (half_pos hr).le ht₀ 2
    have hab : a*b≤1/4 := by dsimp only [b]; nlinarith [sq_nonneg (a-1/2)]
    nlinarith only [mul_le_mul_of_nonneg_right hab (pow_nonneg hr.le 4),mul_le_mul_of_nonneg_left h₀ (sq_nonneg r),sq_nonneg (r^2)]

private theorem near_foot_bound {m n μ R T V y : ℝ} (hm : 0 < m) (hn : 0 < n)
    (hn₁ : n ≤ 1) (hμ : 0 < μ) (hμm : μ ≤ m) (hR : 0 < R)
    (hT : 1/4 ≤ T) (hV : m/4 ≤ V) (hy : |y| ≤ R) :
    2*m*n*y^2/(R^2*T^2*V^2) ≤ 512/μ ∧ 2*m*n*|y|/(R^2*T^2*V) ≤ 128/R := by
  have hT' : 0 < T := by linarith
  have hV' : 0 < V := by linarith
  have hT₂ := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/4) hT 2
  have hV₂ := pow_le_pow_left₀ (by positivity : 0 ≤ m/4) hV 2
  have hd₁ := mul_le_mul hT₂ hV₂ (sq_nonneg _) (sq_nonneg _)
  have hd₂ := mul_le_mul hT₂ hV (by positivity) (sq_nonneg _)
  have hy₂ := pow_le_pow_left₀ (abs_nonneg _) hy 2
  rw [sq_abs] at hy₂
  constructor
  · apply le_trans _ (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 512) hμ hμm)
    apply (div_le_div_iff₀ (by positivity) hm).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hd₁ (sq_nonneg R),
      mul_le_mul_of_nonneg_left hy₂ (by positivity : 0 ≤ m^2*n),
      mul_le_mul_of_nonneg_left hn₁ (by positivity : 0 ≤ m^2*R^2)]
  · apply (div_le_div_iff₀ (by positivity) hR).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hd₂ (sq_nonneg R),
      mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ m*n*R),
      mul_le_mul_of_nonneg_left hn₁ (by positivity : 0 ≤ m*R^2)]

/-- Uniform two-foot, bulk, and far-field estimates in Appendix E.3(a).
The second foot is the real projection of the deeper pole. -/
theorem edge_source_separated_feet {s γ : ℝ} (hg : γ∈Icc 0 (π/2))
    (hc : 1/2 ≤ cos γ) {z : ℂ} (hz : 0 < z.im) :
    let a := normalMass s
    let μ := min a (1-a)
    let r₀ := μ*cos γ/8
    let H := crossSource a (direction γ) z
    let d := ‖z-(cos γ:ℂ)‖
    (‖z‖ < r₀ → |H.re| ≤ 512/μ ∧ ‖H‖ ≤ 128/‖z‖) ∧
    (d < r₀ → |H.re| ≤ 512/μ ∧ ‖H‖ ≤ 128/d) ∧
    (r₀ ≤ ‖z‖ → r₀ ≤ d → ‖H‖ ≤ 2048/μ) ∧
    (2 ≤ ‖z‖ → ‖H‖ ≤ 4/‖z‖^4) := by
  let a := normalMass s
  let b := 1-a
  let μ := min a b
  let c := cos γ
  let q := direction γ
  let r := ‖z‖
  let d := ‖z-(c:ℂ)‖
  let t := ‖z-q‖
  let v := ‖z-(a:ℂ)*q‖
  let Y := z.re*sin γ + z.im*c
  have ha : 0 < a := Certificate.normalMass_pos s
  have hb : 0 < b := by dsimp [a,b]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _
  have ha₁ : a ≤ 1 := by dsimp only [b] at hb; linarith
  have hb₁ : b ≤ 1 := by dsimp only [b]; linarith
  have hμ : 0 < μ := lt_min ha hb
  have hμa : μ ≤ a := min_le_left .. 
  have hμb : μ ≤ b := min_le_right ..
  have hc₁ : c ≤ 1 := cos_le_one _
  have hc₀ : 0 < c := by change 1/2 ≤ c at hc; linarith
  have hs := sin_nonneg_of_nonneg_of_le_pi hg.1 (hg.2.trans (by linarith [pi_pos]))
  have hqr : q.re=c := by simp [q,c,direction,Complex.exp_re,Complex.mul_re]
  have hqi : q.im= -sin γ := direction_im _
  have hr : 0 < r := norm_pos_iff.mpr (fun e => by simp [e] at hz)
  have hd : 0 < d := norm_pos_iff.mpr (fun e => by simpa [sub_eq_zero.mp e] using hz)
  have ht : 0 < t := by
    apply lt_of_lt_of_le _ (Complex.im_le_norm _)
    simp [Complex.sub_im,hqi]; linarith
  have hv : 0 < v := by
    apply lt_of_lt_of_le _ (Complex.im_le_norm _)
    simp [Complex.sub_im,Complex.mul_im,hqi]; nlinarith [mul_nonneg ha.le hs]
  have hdt : d ≤ t := by
    have hsq : d^2 ≤ t^2 := by
      simp [d,t,Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,hqr,hqi]
      nlinarith [mul_nonneg hz.le hs,sq_nonneg (sin γ)]
    by_contra! h
    nlinarith [mul_pos (sub_pos.mpr h) (add_pos hd ht)]
  have hx : z.re ≤ r := Complex.re_le_norm _
  have hcx : c-z.re ≤ d := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (z-(c:ℂ)))).1
    simp only [Complex.sub_re,Complex.ofReal_re] at h; linarith
  have hvx := abs_le.mp (Complex.abs_re_le_norm (z-(a:ℂ)*q))
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hqr] at hvx
  change -v ≤ z.re-a*c ∧ z.re-a*c ≤ v at hvx
  obtain ⟨_,hreal,hneg,habs,hY⟩ := cross_source_claim s γ hg hz
  change _= -2*a*b*Y^2/(r^2*t^2*v^2) at hreal
  change _=2*a*b*|Y|/(r^2*t^2*v) at habs
  change |Y| ≤ min r (min t v) at hY
  have hYr := hY.trans (min_le_left ..)
  have hYt := hY.trans ((min_le_right ..).trans (min_le_left ..))
  have hYv := hY.trans ((min_le_right ..).trans (min_le_right ..))
  dsimp only
  rw [abs_of_nonpos hneg,hreal,habs]
  change (r < μ*c/8 → -(-2*a*b*Y^2/(r^2*t^2*v^2)) ≤ 512/μ ∧ _) ∧ _
  have hreal' : -(-2*a*b*Y^2/(r^2*t^2*v^2))=2*a*b*Y^2/(r^2*t^2*v^2) := by ring
  rw [hreal']
  have hmc₁ := mul_le_mul_of_nonneg_right hμa hc₀.le
  have hmc₂ := mul_le_mul_of_nonneg_right hμb hc₀.le
  have hmc₃ := mul_le_mul_of_nonneg_right (hμa.trans ha₁) hc₀.le
  have hac := mul_le_mul_of_nonneg_left hc ha.le
  have hbc := mul_le_mul_of_nonneg_left hc hb.le
  change a*(1/2) ≤ a*c at hac
  change b*(1/2) ≤ b*c at hbc
  have habc : a*c+b*c=c := by dsimp only [b]; ring
  have hcan : 2*a*b*|Y|/(r^2*t^2*v) ≤ 2*a*b/(r^2*t^2) := by
    calc
      _ ≤ 2*a*b*v/(r^2*t^2*v) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hYv (by positivity)) (by positivity)
      _ = _ := mul_div_mul_right _ _ hv.ne'
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    change r < μ*c/8 at h
    exact near_foot_bound ha hb hb₁ hμ hμa hr
      (by change 1/2 ≤ c at hc; linarith) (by linarith [hvx.1]) hYr
  · intro h
    change d < μ*c/8 at h
    have hh := near_foot_bound hb ha ha₁ hμ hμb ht
      (T:=r) (V:=v) (by change 1/2 ≤ c at hc; linarith) (by linarith [hvx.2]) hYt
    refine ⟨?_,?_⟩
    · convert hh.1 using 1 <;> ring
    · apply le_trans _ (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 128) hd hdt)
      convert hh.2 using 1 <;> ring
  · intro h₁ h₂
    change μ*c/8 ≤ r at h₁
    change μ*c/8 ≤ d at h₂
    apply hcan.trans
    have hsum := norm_sub_le_norm_sub_add_norm_sub q z 0
    simp only [sub_zero,direction_norm,q] at hsum
    rw [norm_sub_rev] at hsum
    change 1 ≤ t+r at hsum
    have hp : μ/32 ≤ r*t := by
      have hμc := mul_le_mul_of_nonneg_left hc hμ.le
      change μ*(1/2) ≤ μ*c at hμc
      rcases le_total r t with h|h
      · nlinarith only [mul_le_mul_of_nonneg_left (show 1/2 ≤ t by linarith) hr.le,h₁,hμc]
      · nlinarith only [mul_le_mul_of_nonneg_left (show 1/2 ≤ r by linarith) ht.le,h₂,hdt,hμc]
    have hab : a*b ≤ μ := le_min (by nlinarith [mul_le_mul_of_nonneg_left hb₁ ha.le])
      (by nlinarith [mul_le_mul_of_nonneg_right ha₁ hb.le])
    apply (div_le_div_iff₀ (by positivity) hμ).mpr
    nlinarith only [pow_le_pow_left₀ (by positivity : 0 ≤ μ/32) hp 2,
      mul_le_mul_of_nonneg_right hab hμ.le]
  · intro h
    change 2 ≤ r at h
    apply hcan.trans
    have hh := norm_sub_le_norm_sub_add_norm_sub z q 0
    simp only [sub_zero,show ‖q‖=1 from direction_norm γ] at hh
    change r ≤ t+1 at hh
    have hab : a*b ≤ 1/4 := by dsimp only [b]; nlinarith [sq_nonneg (a-1/2)]
    apply (div_le_div_iff₀ (by positivity) (by positivity : 0 < r^4)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hab (pow_nonneg hr.le 4),
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (half_pos hr).le (show r/2 ≤ t by linarith) 2) (sq_nonneg r),
      sq_nonneg (r^2)]

end Liu
