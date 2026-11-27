module

public import Liu.AngularModel

@[expose] public section

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

private theorem sine_energy_error {x : ℝ} (hx : 0<x) (hx1 : x≤1) :
    |((x/sin x)^2-1)/x^2-1/3| ≤ 4*x^2 := by
  let d := (x-sin x)/x^3
  let s := sin x/x
  have hTaylor := Real.sin_bound (x:=x) (by simpa [abs_of_pos hx] using hx1)
  rw [abs_of_pos hx] at hTaylor
  have hd : |d-1/6| ≤ x^2/100 := by
    have he : d-1/6 = -(sin x-(x-x^3/6))/x^3 := by dsimp [d]; field_simp [hx.ne']; ring
    rw [he,abs_div,abs_neg,abs_of_pos (pow_pos hx 3)]
    apply (div_le_iff₀ (pow_pos hx 3)).mpr
    linarith only [hTaylor,show x^5/100=x^2/100*x^3 by ring]
  have hxx : x^2≤1 := by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  have hd0 : 0≤d := by linarith [(abs_le.mp hd).1]
  have hd1 : d≤1/2 := by linarith [(abs_le.mp hd).2]
  have he : 1-s=x^2*d := by dsimp [s,d]; field_simp [hx.ne']
  have hslow : 1/2≤ s := by nlinarith [mul_le_mul hxx hd1 hd0 (by norm_num : (0:ℝ)≤1)]
  have hs1 : s≤1 := by nlinarith [mul_nonneg (sq_nonneg x) hd0]
  have hs : 0<s := by linarith
  have hsin : sin x = s*x := by dsimp [s]; field_simp [hx.ne']
  have eqn : ((x/sin x)^2-1)/x^2-1/3 =
      ((d-1/6)*(1+s)+(1-s)*(1+2*s)/6)/s^2 := by
    rw [hsin]
    field_simp [hs.ne',hx.ne']
    nlinarith only [congrArg (fun v : ℝ => v*(1+s)) he]
  rw [eqn,abs_div,abs_of_pos (sq_pos_of_pos hs)]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  apply (abs_add_le ..).trans
  rw [abs_mul,abs_of_pos (by linarith : 0<1+s),abs_of_nonneg (by have := sub_nonneg.mpr hs1; positivity : 0≤(1-s)*(1+2*s)/6)]
  have hmain := mul_le_mul hd (show 1+s≤2 by linarith) (by linarith : 0≤1+s) (by positivity)
  have herr := mul_le_mul (show 1-s≤x^2/2 by nlinarith [mul_le_mul_of_nonneg_left hd1 (sq_nonneg x)])
    (show 1+2*s≤3 by linarith) (by linarith : 0≤1+2*s) (by positivity)
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hslow 2
  nlinarith only [hmain,herr,mul_le_mul_of_nonneg_left hsq (sq_nonneg x),sq_nonneg x]

/-- The angular energy has the printed first-order term with a uniform quadratic remainder. -/
theorem angularEnergy_expansion {t : ℝ} (ht : 0<t) (hx : t*π≤1) :
    |angularEnergy t-k₀*(1+2*t)| ≤ (4*π^4+k₀)*t^2 := by
  have ht1 : t<1 := by nlinarith [pi_gt_three,mul_lt_mul_of_pos_left pi_gt_three ht]
  let x := t*π
  let F := ((x/sin x)^2-1)/x^2
  have hxp : 0<x := mul_pos ht pi_pos
  have h := sine_energy_error hxp hx
  have hrep : angularEnergy t = (1+t)^2*(π^2/4)*F := by
    rw [angularEnergy_eq ht ht1]
    dsimp [F,x]
    field_simp [ht.ne',pi_ne_zero] <;> ring
  have he : angularEnergy t-k₀*(1+2*t) =
      ((1+t)^2*(π^2/4))*(F-1/3)+k₀*t^2 := by rw [hrep]; unfold k₀; ring
  rw [he]
  apply (abs_add_le ..).trans
  have hk : 0≤k₀ := by unfold k₀; positivity
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(1+t)^2*(π^2/4)),abs_of_nonneg (by positivity : 0≤k₀*t^2)]
  have hfac : (1+t)^2*(π^2/4) ≤ π^2 := by
    have hq := pow_le_pow_left₀ (by positivity : 0≤1+t) (by linarith : 1+t≤2) 2
    nlinarith only [mul_le_mul_of_nonneg_right hq (sq_nonneg π)]
  have hh := mul_le_mul hfac h (abs_nonneg (F-1/3)) (sq_nonneg π)
  change _ ≤ _ at hh
  dsimp only [x] at hh
  linarith only [hh,show π^2*(4*(t*π)^2)+k₀*t^2=(4*π^4+k₀)*t^2 by ring]

theorem angularEnergy_slope :
    Tendsto (fun t : ℝ => (angularEnergy t-k₀)/(2*t)) (𝓝[>] 0) (𝓝 k₀) := by
  have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hsmall := h0.eventually_lt_const (inv_pos.mpr pi_pos)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by
    simpa using h0.const_mul ((4*π^4+k₀)/2))
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),hsmall] with t ht hs
  have ht0 : 0<t := ht
  have hx : t*π≤1 := by exact ((lt_div_iff₀ pi_pos).mp (by simpa [one_div] using hs)).le
  have h := angularEnergy_expansion ht0 hx
  rw [Real.norm_eq_abs,show (angularEnergy t-k₀)/(2*t)-k₀=(angularEnergy t-k₀*(1+2*t))/(2*t) by field_simp [ht0.ne']; ring,
    abs_div,abs_of_pos (by positivity : 0<2*t)]
  apply (div_le_iff₀ (by positivity : 0<2*t)).mpr
  linarith only [h,show ((4*π^4+k₀)/2)*t*(2*t)=(4*π^4+k₀)*t^2 by ring]

end Liu
