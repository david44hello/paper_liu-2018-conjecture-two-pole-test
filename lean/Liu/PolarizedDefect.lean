module

public import Liu.GreenVariation

@[expose] public section

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate Topology
namespace Liu

/-- Real polarized integrand of Appendix B, Step 2, before the factor of four in the energy. -/
def PickSum.polarizedDefect {n : ℕ} (p : PickSum n) (t : ℝ) (z : ℂ) : ℝ :=
  let v := greenOperator (p.frozenError t) z
  let r := conj (dbar (logInput (p.power (1+t))) z)
  2*(r*conj v).re + (p.frozenError t z*conj v).re

theorem PickSum.polarizedDefect_factor {n : ℕ} (p : PickSum n) (t : ℝ) {z : ℂ} (hz : 0≤z.im) :
    p.polarizedDefect t z = 2*(dbar (logInput p.value) z).re*
      (p.parameterFactor t z * greenOperator (p.frozenError t) z).re := by
  let v := greenOperator (p.frozenError t) z
  let a := p.parameterFactor t z
  let b := dbar (logInput p.value) z
  have hρ : dbar (logInput (p.power (1+t))) z = a*b := (p.critical_source_identity t hz).1
  have hd : p.frozenError t z = conj a*(b-conj b) := p.frozenError_factor t hz
  change 2*(conj (dbar (logInput (p.power (1+t))) z)*conj v).re + (p.frozenError t z*conj v).re = 2*b.re*(a*v).re
  rw [hρ,hd]
  simp [Complex.mul_re,Complex.mul_im]; ring

private theorem product_real_bound (a v u : ℂ) (hu : u.re=0) :
    |(a*v).re| ≤ ‖a-1‖*‖v‖+‖v-u‖ := by
  calc
    _ = |(a*v-u).re| := by simp [hu]
    _ ≤ ‖a*v-u‖ := Complex.abs_re_le_norm _
    _ = ‖(a-1)*v+(v-u)‖ := by congr 1; ring
    _ ≤ _ := by simpa only [norm_mul] using norm_add_le ((a-1)*v) (v-u)

theorem PickSum.polarizedDefect_bound {n : ℕ} (p : PickSum n) :
    ∃ K ≥ 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ z : ℂ, 0≤z.im →
      |p.polarizedDefect t z| ≤ t*(K*(1+log (2+‖z‖))/(1+‖z‖)^3) := by
  obtain ⟨A,hA,ha⟩ := p.parameterFactor_sub_one
  obtain ⟨C,hC,hc⟩ := p.frozenGreen_estimate
  obtain ⟨D,hD,hd⟩ := p.frozenGreen_lipschitz_zero
  have hder : 0≤p.derivativeBound/2 := by
    simpa using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  refine ⟨(2*(p.derivativeBound/2))*(A*C+D),by positivity,?_⟩
  intro t ht z hz
  let W := 1+‖z‖
  let L := 1+log (2+‖z‖)
  have hW : 0<W := by dsimp [W]; positivity
  have hL : 1≤L := by dsimp [L]; linarith [log_nonneg (show 1≤2+‖z‖ by linarith [norm_nonneg z])]
  have hheight (M : ℝ) (hM : 0≤M) : M*z.im/W^2 ≤ M/W := by
    have hi : z.im ≤ W := (Complex.im_le_norm z).trans (by dsimp [W]; linarith)
    calc
      _ ≤ M*W/W^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi hM) (sq_nonneg _)
      _ = _ := by field_simp [hW.ne']
  let a := p.parameterFactor t z
  let v := greenOperator (p.frozenError t) z
  let u := greenOperator (p.frozenError 0) z
  have hu := congrArg Complex.re (p.green_error_zero_conj z)
  have hur : u.re=0 := by dsimp only [u]; simp only [Complex.conj_re,Complex.neg_re] at hu; linarith
  have hvt : ‖v‖ ≤ C/W := (hc t ht _ (by simp) z hz).2.trans (hheight C hC)
  have hdif : ‖v-u‖ ≤ t*(D/W) :=
    (hd t ht z hz).trans (mul_le_mul_of_nonneg_left (hheight D hD) ht.1)
  have hmul : |(a*v).re| ≤ t*((A*C+D)*L/W) := by
    apply (product_real_bound a v u hur).trans
    have hh := mul_le_mul (ha t ht z hz) hvt (norm_nonneg _) (mul_nonneg ht.1 (mul_nonneg hA.le (by change 0≤L; linarith)))
    change ‖a-1‖*‖v‖ ≤ t*(A*L)*(C/W) at hh
    apply (add_le_add hh hdif).trans
    have hDl : D ≤ D*L := le_mul_of_one_le_right hD hL
    calc
      _ ≤ t*(A*L)*(C/W)+t*((D*L)/W) := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hDl hW.le) ht.1)
      _ = _ := by ring
  have h1 : p.power 1 = p.value := by funext w; simp [PickSum.power]
  have hb := p.power_dbar_decay (ε:=0) (le_refl _) hz
  simp only [add_zero,one_mul,rpow_zero,rpow_ofNat,h1] at hb
  change ‖dbar (logInput p.value) z‖ ≤ (p.derivativeBound/2)/W^2 at hb
  have hfac := (Complex.abs_re_le_norm _).trans hb
  rw [p.polarizedDefect_factor t hz,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  calc
    _ ≤ (2*((p.derivativeBound/2)/W^2))*(t*((A*C+D)*L/W)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hfac (by norm_num)) hmul (abs_nonneg _) (by positivity)
    _ = _ := by change _ = t*(((2*(p.derivativeBound/2))*(A*C+D))*L/W^3); field_simp [hW.ne'] <;> ring

def logTail (z : ℂ) := (1+log (2+‖z‖))/(1+‖z‖)^3

private theorem logTail_nonneg (z : ℂ) : 0≤logTail z := by
  have h := log_nonneg (show 1≤2+‖z‖ by linarith [norm_nonneg z])
  unfold logTail; positivity

theorem logTail_integrable : Integrable logTail upperArea := by
  have hm : Measurable logTail := by unfold logTail; fun_prop
  have h := (integrable_one_add_norm (μ:=(volume:Measure ℂ)) (r:=5/2) (by norm_num)).const_mul (3+log 2)
  have hi : Integrable logTail volume := h.mono' hm.aestronglyMeasurable (by
    filter_upwards with w
    let R := 1+‖w‖
    have hr : 1≤R := by dsimp [R]; linarith [norm_nonneg w]
    have hR := zero_lt_one.trans_le hr
    have hu := one_le_rpow hr (by norm_num : 0≤(1/2:ℝ))
    have hs := log_le_rpow_div hR.le (by norm_num : (0:ℝ)<1/2)
    have hl := log_le_log (by positivity : 0 < 2+‖w‖) (show 2+‖w‖ ≤ 2*R by dsimp [R]; linarith [norm_nonneg w])
    rw [log_mul (by norm_num) hR.ne'] at hl
    rw [Real.norm_eq_abs,abs_of_nonneg (logTail_nonneg _)]
    change (1+log (2+‖w‖))/R^3 ≤ (3+log 2)*R^(-(5/2:ℝ))
    apply (div_le_iff₀ (pow_pos hR 3)).mpr
    rw [show R^(3:ℕ)=R^(3:ℝ) by norm_num,mul_assoc,←rpow_add hR]
    norm_num
    nlinarith [mul_nonneg (log_nonneg (by norm_num : (1:ℝ)≤2)) (sub_nonneg.mpr hu)])
  unfold upperArea area
  rw [Measure.restrict_smul]
  exact hi.restrict.smul_measure ENNReal.ofReal_ne_top

/-- The actual integrated polarized expression, including its critical endpoint,
is O(ε). This estimate uses the two sources and the normalized Green kernel. -/
theorem PickSum.polarizedDefect_integral {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ t ∈ Icc (0:ℝ) 1, Integrable (p.polarizedDefect t) upperArea ∧
      |∫ z, p.polarizedDefect t z ∂upperArea| ≤ C*t := by
  obtain ⟨K,hK,h⟩ := p.polarizedDefect_bound
  have hI : 0≤∫ z, logTail z ∂upperArea := integral_nonneg logTail_nonneg
  refine ⟨K*∫ z, logTail z ∂upperArea,by positivity,?_⟩
  intro t ht
  have hm := (p.frozenError_measurable t).1
  have hg := greenOperator_measurable hm
  have hρ := dbar_measurable (logInput (p.power (1+t)))
  have hf : Measurable (p.polarizedDefect t) := by
    let v := greenOperator (p.frozenError t)
    let r := dbar (logInput (p.power (1+t)))
    have hv : Measurable (fun z => conj (v z)) := Complex.continuous_conj.measurable.comp hg
    have hr : Measurable (fun z => conj (r z)) := Complex.continuous_conj.measurable.comp hρ
    exact (measurable_const.mul (Complex.measurable_re.comp (hr.mul hv))).add
      (Complex.measurable_re.comp (hm.mul hv))
  have hb : ∀ᵐ z ∂upperArea, ‖p.polarizedDefect t z‖ ≤ (t*K)*logTail z := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    rw [Real.norm_eq_abs]
    apply (h t ht z (le_of_lt hz)).trans_eq
    unfold logTail; ring
  have hi := logTail_integrable.const_mul (t*K)
  refine ⟨hi.mono' hf.aestronglyMeasurable hb,?_⟩
  have hn := norm_integral_le_of_norm_le hi hb
  rw [Real.norm_eq_abs,integral_const_mul] at hn
  linarith only [hn,show (t*K)*(∫ z, logTail z ∂upperArea) = (K*∫ z, logTail z ∂upperArea)*t by ring]

end Liu
