import Liu.FirstOrderExpansion

noncomputable section
open Set Real MeasureTheory
open scoped ComplexConjugate Topology
namespace Liu

/-- Each factor in the linearized pairing has an extra power of decay after
the two asymptotic pole directions cancel. -/
theorem linearPairing_integrable {p q : ℂ} (hp : p.im<0) (hq : q.im<0) :
    let A := pole 1 p
    let B := pole 1 q
    Integrable (fun z => field A z*conj (linearBlend (A z) (B z))) upperArea := by
  let A := pole 1 p
  let B := pole 1 q
  let a := poleBound 1 p
  let b := poleBound 1 q
  let d := ‖q-p‖
  let g := fun z => linearBlend (A z) (B z)
  have hg : Measurable g := by dsimp [g,linearBlend,A,B,pole]; fun_prop
  have ha : 0≤a := by dsimp [a,poleBound]; have := neg_pos.mpr hp; positivity
  have hb : 0≤b := by dsimp [b,poleBound]; have := neg_pos.mpr hq; positivity
  let K := (5/2)*a*(a+π*b)*d*b
  have hI := (integrable_one_add_norm (r:=3) (μ:=(volume:Measure ℂ)) (by norm_num)).const_mul K
  have hJ : Integrable (fun z : ℂ => K*(1+‖z‖)^(-(3:ℝ))) upperArea :=
    (hI.smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).restrict
  apply hJ.mono' ((field_measurable A).mul (Complex.continuous_conj.measurable.comp hg)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
  let r := 1+‖z‖
  have hr : 0<r := by dsimp [r]; positivity
  let e := (q-p)/(z-q)
  have hn {w : ℂ} (hw : w.im<0) : z-w≠0 :=
    sub_ne_zero.mpr fun h => by have := (show 0<z.im from hz); rw [h] at this; linarith
  have hA : ‖A z‖≤a/r := pole_global_decay zero_lt_one hp (le_of_lt hz)
  have hB : ‖B z‖≤b/r := pole_global_decay zero_lt_one hq (le_of_lt hz)
  have he : B z/A z=1+e := by dsimp [A,B,e,pole]; push_cast; field_simp [hn hp,hn hq]; ring
  have heu : ‖e‖≤d*(b/r) := by
    have he' : ‖e‖=d*‖B z‖ := by simp [e,d,B,pole,norm_div,div_eq_mul_inv]
    rw [he']; exact mul_le_mul_of_nonneg_left hB (norm_nonneg _)
  have hθ : |(1+e).arg|≤π*‖e‖ := by
    by_cases hh : ‖e‖≤1
    · exact (arg_one_add_bound hh).trans (mul_le_mul_of_nonneg_right (by linarith [pi_pos]) (norm_nonneg _))
    · exact (Complex.abs_arg_le_pi _).trans (le_mul_of_one_le_right pi_pos.le (le_of_not_ge hh))
  have hα := upper_arg_div (show B z∈upper from pole_im_pos zero_lt_one hq (le_of_lt hz))
    (show A z∈upper from pole_im_pos zero_lt_one hp (le_of_lt hz))
  rw [he] at hα
  have hg' : ‖g z‖≤(a/r+π*(b/r))*(d*(b/r)) := by
    change ‖A z*_+B z*_‖≤_
    apply (norm_add_le ..).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,he,Complex.add_im,Complex.one_im,zero_add,
      abs_sub_comm (A z).arg,←hα]
    have h₁ := mul_le_mul hA (Complex.abs_im_le_norm e) (abs_nonneg _) (div_nonneg ha hr.le)
    have h₂ := mul_le_mul hB hθ (abs_nonneg _) (div_nonneg hb hr.le)
    have h₃ := mul_le_mul_of_nonneg_left heu (show 0≤a/r+π*(b/r) by positivity)
    nlinarith only [h₁,h₂,h₃]
  have hv := (onePole_field_bound hp (le_of_lt hz)).trans (mul_le_mul_of_nonneg_left hA (by norm_num))
  change ‖field A z*conj (g z)‖≤_
  rw [norm_mul,Complex.norm_conj]
  apply (mul_le_mul hv hg' (norm_nonneg _) (by positivity)).trans_eq
  change _=K*r^(-(3:ℝ))
  rw [Real.rpow_neg hr.le,Real.rpow_ofNat]; dsimp [K]; ring

end Liu
