module

public import Liu.CapCayley

@[expose] public section

noncomputable section
open Set MeasureTheory Real Metric
open scoped Topology ComplexConjugate
namespace Liu

private theorem disc_boundary_rpow_integrable {q : ℝ} (hq : q<2) :
    Integrable (fun w : ℂ => ‖1-w‖^(-q)) discArea := by
  have hi : IntegrableOn (fun w : ℂ => ‖w‖^(-q)) (ball 0 2) volume := by
    apply integrableOn_ball_of_norm_le_rpow (C:=1) (α:=q) (by simp) (by simpa using hq)
    · exact ae_of_all _ fun w => by simp [abs_of_nonneg (rpow_nonneg (norm_nonneg w) (-q))]
    · exact (show Measurable (fun w : ℂ => ‖w‖^(-q)) by fun_prop).aestronglyMeasurable
  have h := ((measurePreserving_add_right (volume:Measure ℂ) (-(1:ℂ))).integrableOn_comp_preimage
    (Homeomorph.addRight (-(1:ℂ))).measurableEmbedding).mpr hi
  have hs : disc ⊆ (fun w : ℂ => w+ -1) ⁻¹' ball 0 2 := by
    intro w hw
    have hh := norm_sub_le w (1:ℂ)
    have h1 : ‖w‖<1 := by simpa [disc] using hw
    simp only [norm_one] at hh
    change dist (w+ -1) 0<2; rw [dist_zero_right,←sub_eq_add_neg]; linarith
  have hd : IntegrableOn (fun w : ℂ => ‖1-w‖^(-q)) disc volume := by
    simpa only [Function.comp_def,←sub_eq_add_neg,norm_sub_rev (1:ℂ)] using h.mono_set hs
  unfold discArea area; rw [Measure.restrict_smul]; exact hd.smul_measure ENNReal.ofReal_ne_top

theorem disc_log_domination {T : ℝ} (hT : T<2) :
    ∃ B : ℂ → ℝ, Integrable B discArea ∧ ∀ w ∈ disc, ∀ s∈Icc 0 T,
      ‖1-w‖^(-s)*(1+‖discLog w‖)^2 ≤ B w := by
  let δ := (2-T)/4
  have hδ : 0<δ := by dsimp [δ]; linarith
  let q := T+2*δ
  have hq : q<2 := by dsimp [q,δ]; linarith
  let K := 1+π+log 2+δ⁻¹
  have h2 := log_nonneg (by norm_num : (1:ℝ)≤2)
  have hK : 0≤K := by dsimp [K]; positivity
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  have ho : Integrable (fun _ : ℂ => (1:ℝ)) discArea := integrableOn_const (measure_ball_lt_top ..).ne
  refine ⟨fun w => K^2*(1+‖1-w‖^(-q)),(ho.add (disc_boundary_rpow_integrable hq)).const_mul _,?_⟩
  intro w hw s hs
  let r := ‖1-w‖
  have hn : 1-w≠0 := fun he => by rw [←sub_eq_zero.mp he] at hw; simpa [disc] using hw
  have hr : 0<r := norm_pos_iff.mpr hn
  have hr2 : r≤2 := by
    have h := norm_sub_le (1:ℂ) w
    have hw' : ‖w‖<1 := by simpa [disc] using hw
    dsimp only [r]; simpa only [norm_one] using h.trans (by rw [norm_one]; linarith : ‖(1:ℂ)‖+‖w‖≤2)
  have hlog : ‖discLog w‖ ≤ |log r|+π := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    simp only [discLog,Complex.log_re,Complex.log_im,r]
    exact add_le_add le_rfl (Complex.abs_arg_le_pi _)
  by_cases small : r≤1
  · have hu := rpow_le_one hr.le small hδ.le
    have hl := (abs_log_mul_self_rpow_lt r δ hr small hδ).le
    rw [abs_mul,abs_of_nonneg (rpow_nonneg hr.le δ),one_div] at hl
    have hb : (1+‖discLog w‖)*r^δ≤K := by
      dsimp only [K]; nlinarith only [mul_le_mul_of_nonneg_right hlog (rpow_nonneg hr.le δ),hl,hu,mul_le_mul_of_nonneg_left hu pi_pos.le,h2]
    have hsq := pow_le_pow_left₀ (by positivity) ((le_div_iff₀ (rpow_pos_of_pos hr δ)).mpr hb) 2
    have hpow : r^(-s)≤r^(-T) := rpow_le_rpow_of_exponent_ge hr small (neg_le_neg hs.2)
    apply (mul_le_mul hpow hsq (sq_nonneg _) (rpow_nonneg hr.le _)).trans
    have he : r^(-T)*(K/r^δ)^2=K^2*r^(-q) := by
      rw [div_pow,←rpow_ofNat (r^δ) 2,←rpow_mul hr.le,div_eq_mul_inv,←rpow_neg hr.le]
      dsimp only [q]; rw [mul_left_comm,←rpow_add hr]; congr 2; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (by linarith : r^(-q)≤1+r^(-q)) (sq_nonneg _)
  · have large := le_of_not_ge small
    have hs' := rpow_le_one_of_one_le_of_nonpos large (neg_nonpos.mpr hs.1)
    have hb : 1+‖discLog w‖≤K := by
      rw [abs_of_nonneg (log_nonneg large)] at hlog
      dsimp only [K]; linarith [log_le_log hr hr2,inv_nonneg.mpr hδ.le]
    apply ((mul_le_of_le_one_left (sq_nonneg _) hs').trans (pow_le_pow_left₀ (by positivity) hb 2)).trans
    exact le_mul_of_one_le_right (sq_nonneg _) (by linarith [rpow_nonneg hr.le (-q)] : 1≤1+r^(-q))

theorem discPower_hasDerivAt (a : ℝ) {z : ℂ} (hz : z∈disc) :
    HasDerivAt (fun u : ℝ => discPower u z) (-discLog z*discPower a z) a := by
  have hn : 1-z≠0 := fun he => by rw [←sub_eq_zero.mp he] at hz; simpa [disc] using hz
  have he : (fun u : ℝ => discPower u z) = fun u : ℝ => Complex.exp (-(discLog z)*(u:ℂ)) := by
    funext u; simp [discPower,discLog,Complex.cpow_def_of_ne_zero hn,one_div,neg_mul,Complex.exp_neg]
  have hh := (((hasDerivAt_id (a:ℂ)).const_mul (-discLog z)).cexp).comp_ofReal
  change HasDerivAt (fun u : ℝ => discPower u z) (-discLog z*((fun u : ℝ => discPower u z) a)) a
  rw [he]; simpa [mul_comm] using hh

theorem discPower_norm (a : ℝ) (z : ℂ) : ‖discPower a z‖=‖1-z‖^(-a) := by
  rw [discPower,norm_div,norm_one,Complex.norm_cpow_real,rpow_neg (norm_nonneg _),one_div]

end Liu
