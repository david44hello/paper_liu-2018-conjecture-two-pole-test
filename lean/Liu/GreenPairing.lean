import Liu.GreenVariation

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

/-- Uniform absolute Green bound for an integrable source with a quadratic
pointwise envelope. The constant may depend on the source's L¹ norm. -/
theorem green_L1_bound {f : ℂ → ℂ} (hf : Integrable f upperArea) (hm : Measurable f)
    {K : ℝ} (hK : 0≤K) (hsrc : ∀ w ∈ upper, ‖f w‖ ≤ K/(1+‖w‖)^2) :
    ∃ M ≥ 0, ∀ z : ℂ, 0≤z.im → Integrable (fun w => (greenLog z w:ℂ)*f w) upperArea ∧
      (∫ w, ‖(greenLog z w:ℂ)*f w‖ ∂upperArea) ≤ M := by
  let A := ∫ w, localInverse 0 w
  have hA : 0≤A := integral_nonneg fun w => indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _
  have hf0 : 0≤∫ w, ‖f w‖ ∂upperArea := integral_nonneg fun _ => norm_nonneg _
  refine ⟨8*K*(1/π)*A + 4*∫ w, ‖f w‖ ∂upperArea,by positivity,?_⟩
  intro z hz
  let R := 1+‖z‖
  have hr : 0<R := by dsimp [R]; positivity
  have hy : z.im ≤ R := (Complex.im_le_norm _).trans (by dsimp [R]; linarith)
  let L := fun w : ℂ => localInverse (R⁻¹ • z) (R⁻¹ • w)
  have hi : Integrable L volume := (localInverse_integrable _).comp_smul (inv_ne_zero hr.ne')
  have hia : Integrable L area := hi.smul_measure ENNReal.ofReal_ne_top
  have hL : ∀ w, 0≤L w := fun w => indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _
  have hli : (∫ w, L w ∂upperArea) ≤ (1/π)*(R^2*A) := by
    apply (integral_mono_measure Measure.restrict_le_self (ae_of_all area hL) hia).trans_eq
    simp only [area,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤1/π),smul_eq_mul]
    have he : (∫ w, L w) = R^2*A := by
      simpa [L,A] using scaled_localInverse_integral (R⁻¹ • z) R⁻¹ (inv_pos.mpr hr)
    rw [he]
  let g := fun w => (8*K/R^2)*L w + 4*‖f w‖
  have hg : Integrable g upperArea := (hia.restrict.const_mul _).add (hf.norm.const_mul _)
  have hb : ∀ᵐ w ∂upperArea, ‖(greenLog z w:ℂ)*f w‖ ≤ g w := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hk := greenLog_height_bound hz hw
    by_cases near : ‖z-w‖ < R/2
    · apply le_trans _ (le_add_of_nonneg_right (by positivity : 0≤4*‖f w‖))
      have hW : 0<1+‖w‖ := by positivity
      have hgeom : R ≤ 2*(1+‖w‖) := by
        have ht := norm_add_le (z-w) w
        rw [sub_add_cancel] at ht
        dsimp [R] at near ⊢; linarith
      have hsmall : ‖f w‖ ≤ 4*K/R^2 := (hsrc w hw).trans (by
        apply (div_le_div_iff₀ (sq_pos_of_pos hW) (sq_pos_of_pos hr)).mpr
        nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hgeom 2) hK])
      apply (mul_le_mul (hk.trans (mul_le_mul_of_nonneg_right (by linarith : 2*z.im≤2*R)
        (inv_nonneg.mpr (norm_nonneg _)))) hsmall (norm_nonneg _) (by positivity)).trans_eq
      rw [show L w=R*‖z-w‖⁻¹ from scaled_inverse_near hr near]; ring
    · apply le_trans _ (le_add_of_nonneg_left (by have := hL w; positivity : 0≤(8*K/R^2)*L w))
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply hk.trans
      rw [←div_eq_mul_inv]
      apply (div_le_iff₀ (lt_of_lt_of_le (half_pos hr) (le_of_not_gt near))).mpr
      linarith [le_of_not_gt near]
  have hfm : Measurable (fun w => (greenLog z w:ℂ)*f w) := by unfold greenLog; fun_prop
  have hfi := hg.mono' hfm.aestronglyMeasurable hb
  refine ⟨hfi,(integral_mono_ae hfi.norm hg hb).trans ?_⟩
  have hliU : Integrable L upperArea := hia.restrict
  simp only [g,integral_add (hliU.const_mul _) (hf.norm.const_mul _),integral_const_mul]
  apply add_le_add _ le_rfl
  apply (mul_le_mul_of_nonneg_left hli (by positivity : 0≤8*K/R^2)).trans_eq
  field_simp [hr.ne'] <;> ring

/-- The real Green form uses the paper's normalized half-plane area. -/
def greenPairing (f g : ℂ → ℂ) : ℝ := ∫ z, (f z*conj (greenOperator g z)).re ∂upperArea

theorem greenLog_swap (z w : ℂ) : greenLog z w = greenLog w z := by
  have he : ‖z-conj w‖ = ‖w-conj z‖ := by
    rw [←Complex.norm_conj (z-conj w),map_sub,Complex.conj_conj,norm_sub_rev]
  rw [greenLog,greenLog,he,norm_sub_rev z w]

private def pairingKernel (f g : ℂ → ℂ) (q : ℂ × ℂ) : ℝ :=
  (1/2:ℝ)*greenLog q.1 q.2*(f q.1*conj (g q.2)).re

private theorem pairingKernel_integrable {f g : ℂ → ℂ} (hf : Integrable f upperArea)
    (hm : Measurable f) (hgm : Measurable g) {M : ℝ} (hM : 0≤M)
    (hg : ∀ z : ℂ, 0≤z.im → Integrable (fun w => (greenLog z w:ℂ)*g w) upperArea ∧
      (∫ w, ‖(greenLog z w:ℂ)*g w‖ ∂upperArea) ≤ M) :
    Integrable (pairingKernel f g) (upperArea.prod upperArea) := by
  letI : SFinite upperArea := by unfold upperArea area; infer_instance
  have hkm : Measurable (pairingKernel f g) := by unfold pairingKernel greenLog; fun_prop
  have point (z w : ℂ) : ‖pairingKernel f g (z,w)‖ ≤ ‖f z‖*‖(greenLog z w:ℂ)*g w‖ := by
    simp only [pairingKernel,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : 0≤(1/2:ℝ)),norm_mul,
      Complex.norm_real,Real.norm_eq_abs]
    have h := (Complex.abs_re_le_norm (f z*conj (g w))).trans_eq (by rw [norm_mul,Complex.norm_conj])
    calc
      _ ≤ ((1/2)*|greenLog z w|)*(‖f z‖*‖g w‖) := mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ _ := by nlinarith only [mul_nonneg (abs_nonneg (greenLog z w)) (mul_nonneg (norm_nonneg (f z)) (norm_nonneg (g w)))]
  have innerint (z : ℂ) (hz : 0≤z.im) : Integrable (fun w => pairingKernel f g (z,w)) upperArea :=
    ((hg z hz).1.norm.const_mul _).mono' (hkm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (ae_of_all _ (point z))
  apply (integrable_prod_iff hkm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz using innerint z (le_of_lt hz)
  · apply (hf.norm.mul_const M).mono' (hkm.norm.stronglyMeasurable.integral_prod_right' (ν:=upperArea)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    have hpos : 0≤∫ w, ‖pairingKernel f g (z,w)‖ ∂upperArea := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs,abs_of_nonneg hpos]
    have hi := integral_mono_ae (innerint z (le_of_lt hz)).norm ((hg z (le_of_lt hz)).1.norm.const_mul _)
      (ae_of_all _ (point z))
    rw [integral_const_mul] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (hg z (le_of_lt hz)).2 (norm_nonneg _))

/-- Integrable sources with quadratic pointwise decay and measurable representatives. -/
structure GreenSource (f : ℂ → ℂ) : Prop where
  measurable : Measurable f
  integrable : Integrable f upperArea
  decay : ∃ K ≥ 0, ∀ z ∈ upper, ‖f z‖ ≤ K/(1+‖z‖)^2

theorem GreenSource.of_decay {f : ℂ → ℂ} {a K : ℝ} (ha : 2<a) (hK : 0≤K) (hm : Measurable f)
    (h : ∀ z ∈ upper, ‖f z‖ ≤ K/(1+‖z‖)^a) : GreenSource f := by
  have hI := (integrable_one_add_norm (μ:=(volume:Measure ℂ)) (r:=a) (by simpa using ha)).const_mul K
  have hA : Integrable (fun z : ℂ => K*(1+‖z‖)^(-a)) upperArea :=
    (hI.smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).restrict
  refine ⟨hm,hA.mono' hm.aestronglyMeasurable ?_,K,hK,?_⟩
  · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    simpa only [rpow_neg (by positivity : 0≤1+‖z‖),div_eq_mul_inv] using h z hz
  · intro z hz
    apply (h z hz).trans
    apply div_le_div_of_nonneg_left hK (by positivity)
    simpa only [rpow_ofNat] using rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z] : 1≤1+‖z‖) ha.le

theorem GreenSource.conjugate {f : ℂ → ℂ} (h : GreenSource f) : GreenSource (fun w => conj (f w)) := by
  obtain ⟨K,hK,hd⟩ := h.decay
  exact ⟨Complex.continuous_conj.measurable.comp h.measurable,
    Complex.conjCLE.toContinuousLinearMap.integrable_comp h.integrable,K,hK,fun z hz => by simpa using hd z hz⟩

theorem GreenSource.sub {f g : ℂ → ℂ} (hf : GreenSource f) (hg : GreenSource g) : GreenSource (fun w => f w-g w) := by
  obtain ⟨A,hA,ha⟩ := hf.decay
  obtain ⟨B,hB,hb⟩ := hg.decay
  exact ⟨hf.measurable.sub hg.measurable,hf.integrable.sub hg.integrable,A+B,add_nonneg hA hB,fun w hw =>
    (norm_sub_le ..).trans ((add_le_add (ha w hw) (hb w hw)).trans_eq (add_div ..).symm)⟩

private theorem pairingKernel_integral_right {f g : ℂ → ℂ} {z : ℂ}
    (hi : Integrable (fun w => (greenLog z w:ℂ)*g w) upperArea) :
    (∫ w, pairingKernel f g (z,w) ∂upperArea) = (f z*conj (greenOperator g z)).re := by
  let v := fun w => (greenLog z w:ℂ)*g w
  let a : ℂ := (1/2:ℂ)*f z
  have hv : Integrable (fun w => a*conj (v w)) upperArea :=
    (Complex.conjCLE.toContinuousLinearMap.integrable_comp hi).const_mul a
  have he (w : ℂ) : pairingKernel f g (z,w) = (a*conj (v w)).re := by
    simp [pairingKernel,a,v,Complex.mul_re,Complex.mul_im]; ring
  simp_rw [he]
  apply (integral_re hv).trans
  change (∫ w, a*conj (v w) ∂upperArea).re = _
  rw [integral_const_mul,integral_conj]
  change (a*conj (∫ w, v w ∂upperArea)).re = (f z*conj ((1/2:ℝ) • ∫ w, v w ∂upperArea)).re
  simp [a,Complex.real_smul]; congr 1 <;> ring

theorem greenPairing_integrable {f g : ℂ → ℂ} (hf : GreenSource f) (hg : GreenSource g) :
    Integrable (fun z => (f z*conj (greenOperator g z)).re) upperArea := by
  obtain ⟨K,hK,hd⟩ := hg.decay
  obtain ⟨M,hM,h⟩ := green_L1_bound hg.integrable hg.measurable hK hd
  have hk := pairingKernel_integrable hf.integrable hf.measurable hg.measurable hM h
  letI : SFinite upperArea := by unfold upperArea area; infer_instance
  apply hk.integral_prod_left.congr
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz using pairingKernel_integral_right (h z (le_of_lt hz)).1

private theorem greenPairing_eq_double {f g : ℂ → ℂ} (hf : GreenSource f) (hg : GreenSource g) :
    greenPairing f g = ∫ q, pairingKernel f g q ∂upperArea.prod upperArea := by
  obtain ⟨K,hK,hd⟩ := hg.decay
  obtain ⟨M,hM,h⟩ := green_L1_bound hg.integrable hg.measurable hK hd
  have hk := pairingKernel_integrable hf.integrable hf.measurable hg.measurable hM h
  letI : SFinite upperArea := by unfold upperArea area; infer_instance
  rw [integral_prod _ hk,greenPairing]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz using
    (pairingKernel_integral_right (h z (le_of_lt hz)).1).symm

theorem greenPairing_symm {f g : ℂ → ℂ} (hf : GreenSource f) (hg : GreenSource g) :
    greenPairing f g = greenPairing g f := by
  letI : SFinite upperArea := by unfold upperArea area; infer_instance
  rw [greenPairing_eq_double hf hg,greenPairing_eq_double hg hf,←integral_prod_swap (pairingKernel g f)]
  apply integral_congr_ae
  filter_upwards with q
  rcases q with ⟨z,w⟩
  simp only [pairingKernel,Prod.swap,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  rw [greenLog_swap]; ring

theorem greenPairing_sub_left {f g h : ℂ → ℂ} (hf : GreenSource f) (hg : GreenSource g) (hh : GreenSource h) :
    greenPairing (fun w => f w-g w) h = greenPairing f h-greenPairing g h := by
  unfold greenPairing
  simp only [sub_mul,Complex.sub_re,integral_sub (greenPairing_integrable hf hh) (greenPairing_integrable hg hh)]

theorem greenPairing_conj_energy (f : ℂ → ℂ) :
    greenPairing (fun w => conj (f w)) (fun w => conj (f w)) = greenPairing f f := by
  unfold greenPairing
  simp [greenOperator_conj,Complex.mul_re]

end Liu
