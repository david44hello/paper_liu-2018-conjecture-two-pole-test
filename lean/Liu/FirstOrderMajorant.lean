module

public import Liu.UnitTruncation

@[expose] public section

noncomputable section
open Set Real MeasureTheory Metric
open scoped ComplexConjugate
namespace Liu

private def firstCore (p q z : ℂ) : ℂ :=
  let A := pole 1 p
  if ‖z-p‖<‖q-p‖/2 then A z*conj (A z)*firstOrderQ (((A z).arg:ℂ)-optimalWitness A z) else 0

private def firstMajorant (p q z : ℂ) : ℝ :=
  let d := ‖q-p‖
  (10/d)*radialInvDisc (d/2) ‖z-p‖+(20/d)*radialInvDisc (d/2) ‖z-q‖+
    (5*d)*(radialInvTail 3 (2*d/5) ‖z-p‖+radialInvTail 3 (2*d/5) ‖z-q‖)

private theorem firstMajorant_integral {p q : ℂ} (hp : p.im<0) (hq : q.im<0) (hne : q≠p) :
    Integrable (firstMajorant p q) upperArea ∧ (∫ z, firstMajorant p q z ∂upperArea)≤40 := by
  let d := ‖q-p‖
  have hd : 0<d := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have ha : 0<d/2 := by positivity
  have hb : 0<2*d/5 := by positivity
  obtain ⟨h₁,g₁⟩ := radialInvDisc_majorant hp.le ha
  obtain ⟨h₂,g₂⟩ := radialInvDisc_majorant hq.le ha
  obtain ⟨h₃,g₃⟩ := radialInvTail_majorant hp.le hb (k:=3) (by decide)
  obtain ⟨h₄,g₄⟩ := radialInvTail_majorant hq.le hb (k:=3) (by decide)
  have h₁' := h₁.const_mul (10/d)
  have h₂' := h₂.const_mul (20/d)
  have h₃' := (h₃.add h₄).const_mul (5*d)
  refine ⟨(h₁'.add h₂').add h₃',?_⟩
  dsimp only [firstMajorant]
  erw [integral_add (h₁'.add h₂') h₃',integral_add h₁' h₂',integral_const_mul,integral_const_mul,integral_const_mul,integral_add h₃ h₄]
  have H := add_le_add (add_le_add (mul_le_mul_of_nonneg_left g₁ (by positivity : 0≤10/d))
    (mul_le_mul_of_nonneg_left g₂ (by positivity : 0≤20/d)))
    (mul_le_mul_of_nonneg_left (add_le_add g₃ g₄) (by positivity : 0≤5*d))
  apply H.trans_eq
  norm_num [Real.rpow_neg hb.le,Real.rpow_neg_one] <;> field_simp [hd.ne'] <;> ring

private theorem firstCorrected_bound {p q z : ℂ} (hp : p.im<0) (hq : q.im<0) (hne : q≠p) (hz : 0≤z.im) :
    ‖firstOrderIntegrand p q z+firstCore p q z‖≤firstMajorant p q z := by
  let d := ‖q-p‖
  let r := ‖z-p‖
  let t := ‖z-q‖
  have hd : 0<d := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hn {w : ℂ} (hw : w.im<0) : z-w≠0 := sub_ne_zero.mpr fun e => by rw [e] at hz; linarith
  have hr : 0<r := norm_pos_iff.mpr (hn hp)
  have ht : 0<t := norm_pos_iff.mpr (hn hq)
  have htri : d≤r+t := by simpa [d,r,t,norm_sub_rev q z,add_comm] using norm_sub_le_norm_sub_add_norm_sub q z p
  let A := pole 1 p z
  let B := pole 1 q z
  let Q := firstOrderQ ((A.arg:ℂ)-optimalWitness (pole 1 p) z)
  have hQ : ‖Q‖≤5 := firstOrderQ_bound hp hz
  have ha : ‖A‖=1/r := by simp [A,r,pole,norm_div]
  have hb : ‖B‖=1/t := by simp [B,t,pole,norm_div]
  have H := firstOrderIntegrand_bound hp hq hz
  change ‖firstOrderIntegrand p q z‖≤5*d/(r^2*t) at H
  have hi {u : ℝ} (hu : 0<u) : 0≤radialInvDisc (d/2) u := by dsimp [radialInvDisc]; split <;> positivity
  have ht' (u : ℝ) (hu : 0<u) : 0≤radialInvTail 3 (2*d/5) u := by
    dsimp [radialInvTail]; by_cases hh : u∈Ioi (2*d/5) <;> simp [hh]; positivity
  have h₁ : 0≤10/d*radialInvDisc (d/2) r := mul_nonneg (by positivity) (hi hr)
  have h₂ : 0≤20/d*radialInvDisc (d/2) t := mul_nonneg (by positivity) (hi ht)
  have h₃ := mul_nonneg (by positivity : 0≤5*d) (ht' r hr)
  have h₄ := mul_nonneg (by positivity : 0≤5*d) (ht' t ht)
  change _ ≤ 10/d*radialInvDisc (d/2) r+20/d*radialInvDisc (d/2) t+
    5*d*(radialInvTail 3 (2*d/5) r+radialInvTail 3 (2*d/5) t)
  by_cases h : r<d/2
  · have hsum : firstOrderIntegrand p q z+firstCore p q z=A*conj B*Q := by
      dsimp only [firstOrderIntegrand,firstCore]; rw [if_pos h,map_sub]; dsimp [A,B,Q]; ring
    rw [hsum,norm_mul,norm_mul,Complex.norm_conj,ha,hb]
    have hb' : 1/t≤2/d := (div_le_div_iff₀ ht hd).mpr (by linarith)
    have hl := mul_le_mul (mul_le_mul_of_nonneg_left hb' (one_div_nonneg.mpr hr.le)) hQ (norm_nonneg _) (by positivity)
    rw [radialInvDisc,if_pos h.le]
    have he : 1/r*(2/d)*5=10/d*r⁻¹ := by ring
    linarith only [hl,he,h₂,h₃,h₄]
  · rw [show firstCore p q z=0 from if_neg h,add_zero]
    apply H.trans
    have hr' := le_of_not_gt h
    by_cases ho : t≤d/2
    · have he : 5*d/(r^2*t) ≤ 20/d*t⁻¹ := by
        rw [←div_eq_mul_inv,div_div,div_le_div_iff₀ (mul_pos (sq_pos_of_pos hr) ht) (mul_pos hd ht)]
        have H := pow_le_pow_left₀ (half_pos hd).le hr' 2
        nlinarith only [mul_le_mul_of_nonneg_right H ht.le]
      rw [show radialInvDisc (d/2) t=t⁻¹ from if_pos ho]
      linarith only [h₁,h₃,h₄,he]
    · have ht₀ : 2*d/5<t := by linarith [lt_of_not_ge ho]
      have hr₀ : 2*d/5<r := by linarith
      have htq : radialInvTail 3 (2*d/5) t=(t^3)⁻¹ := indicator_of_mem (show t∈Ioi (2*d/5) from ht₀) _
      have hrq : radialInvTail 3 (2*d/5) r=(r^3)⁻¹ := indicator_of_mem (show r∈Ioi (2*d/5) from hr₀) _
      rcases le_total r t with hrt | htr
      · have le : r^3≤r^2*t := by nlinarith only [mul_le_mul_of_nonneg_left hrt (sq_nonneg r)]
        have HH := div_le_div_of_nonneg_left (by positivity : 0≤5*d) (pow_pos hr 3) le
        rw [div_eq_mul_inv (5*d) (r^3),←hrq] at HH
        linarith only [HH,h₁,h₂,h₄]
      · have le : t^3≤r^2*t := by nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.le htr 2) ht.le]
        have HH := div_le_div_of_nonneg_left (by positivity : 0≤5*d) (pow_pos ht 3) le
        rw [div_eq_mul_inv (5*d) (t^3),←htq] at HH
        linarith only [HH,h₁,h₂,h₃]

/-- Uniform control of the real part of the actual integral in C.1. The
potentially large signed core cancels by its single-pole angular mean. -/
theorem firstOrderIntegral_bound {q : ℂ} (hq : q.im<0) :
    Integrable (firstOrderIntegrand (-Complex.I) q) upperArea ∧
    |(∫ z, firstOrderIntegrand (-Complex.I) q z ∂upperArea).re|≤79 := by
  let p := -Complex.I
  have hp : p.im<0 := by simp [p]
  by_cases he : q=p
  · have h : firstOrderIntegrand p q=0 := by rw [he]; funext z; simp [firstOrderIntegrand]
    change Integrable (firstOrderIntegrand p q) upperArea ∧ _
    rw [h]; simp
  let d := ‖q-p‖
  let T := {z : ℂ | ‖z-p‖<d/2}
  let C := firstCore p q
  let Y := firstOrderIntegrand p q
  let A := pole 1 p
  let D := fun z => (A z).arg-optimalWitness A z
  have hmA : Measurable A := by change Measurable (pole 1 p); unfold pole; fun_prop
  have hmB : Measurable (pole 1 q) := by unfold pole; fun_prop
  have hfield := field_measurable A
  have hW : Measurable (optimalWitness A) := by
    unfold optimalWitness; fun_prop
  have hD : Measurable D := by dsimp [D]; apply Measurable.sub _ hW; dsimp [A,pole]; fun_prop
  have hC : Measurable C := by
    dsimp only [C,firstCore]
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) _ measurable_const
    change Measurable (fun z => A z*conj (A z)*firstOrderQ (D z))
    dsimp only [firstOrderQ]; fun_prop
  have hY : Measurable Y := by
    change Measurable (fun z => A z*conj (pole 1 q z-A z)*firstOrderQ (D z))
    dsimp only [firstOrderQ]; fun_prop
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  letI : IsFiniteMeasureOnCompacts upperArea := by unfold upperArea; infer_instance
  have hT : MeasurableSet T := measurableSet_lt (by fun_prop) measurable_const
  have htball : T=ball p (d/2) := by ext z; simp [T,mem_ball,dist_eq_norm]
  have hTfin : upperArea T≠⊤ := htball ▸ (measure_ball_lt_top ..).ne
  have hiC : Integrable C upperArea := by
    have h₅ := (integrable_indicator_iff (μ:=upperArea) hT).mpr (integrableOn_const (C:=(5:ℝ)) hTfin)
    apply h₅.mono' hC.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    by_cases h : z∈T
    · rw [indicator_of_mem h]; dsimp only [C,firstCore]; rw [if_pos (show ‖z-p‖<‖q-p‖/2 from h),norm_mul,norm_mul,Complex.norm_conj]
      have hr : 1≤‖z-p‖ := by apply le_trans _ (Complex.im_le_norm _); simp [p]; exact le_of_lt hz
      have hA : ‖pole 1 p z‖≤1 := by simpa [pole,norm_div] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hr)
      exact (mul_le_mul (mul_le_mul hA hA (norm_nonneg _) zero_le_one) (firstOrderQ_bound hp (le_of_lt hz))
        (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    · rw [indicator_of_notMem h]; dsimp only [C,firstCore]; rw [if_neg (show ¬‖z-p‖<‖q-p‖/2 from h),norm_zero]
  obtain ⟨hM,hM'⟩ := firstMajorant_integral hp hq he
  have hcorrect : ∀ᵐ z ∂upperArea, ‖Y z+C z‖≤firstMajorant p q z := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    exact firstCorrected_bound hp hq he (le_of_lt hz)
  have hi : Integrable (fun z => Y z+C z) upperArea := hM.mono' (hY.add hC).aestronglyMeasurable hcorrect
  have hiY : Integrable Y upperArea := by simpa only [Pi.sub_def,add_sub_cancel_right] using hi.sub hiC
  have hsum := (norm_integral_le_of_norm_le hM hcorrect).trans hM'
  change ‖∫ z, Y z+C z ∂upperArea‖≤40 at hsum
  rw [integral_add hiY hiC] at hsum
  have hRe := (Complex.abs_re_le_norm _).trans hsum
  rw [Complex.add_re] at hRe
  have hpoint : (fun z => (C z).re)=ᵐ[upperArea] T.indicator (witnessDensity unitPolePick.value singleWitness) := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    by_cases h : z∈T
    · rw [indicator_of_mem h]
      dsimp only [C,firstCore]; rw [if_pos (show ‖z-p‖<‖q-p‖/2 from h),Complex.mul_conj',←Complex.ofReal_pow,Complex.re_ofReal_mul,
        firstOrderQ,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,sub_zero]
      rw [witnessDensity,←unitPole_optimalWitness (le_of_lt hz),unitPolePick_value]
    · rw [indicator_of_notMem h]; dsimp only [C,firstCore]; rw [if_neg (show ¬‖z-p‖<‖q-p‖/2 from h)]; rfl
  have hcore : |(∫ z, C z ∂upperArea).re|≤39 := by
    have hr : (∫ z, (C z).re ∂upperArea)=(∫ z, C z ∂upperArea).re := integral_re hiC
    rw [←hr,integral_congr_ae hpoint,integral_indicator hT]
    simpa only [T,p,sub_neg_eq_add] using unitPole_partial_density_bound (d/2)
  refine ⟨hiY,?_⟩
  change |(∫ z, Y z ∂upperArea).re| ≤ 79
  rw [abs_le] at hRe hcore ⊢; constructor <;> linarith [hRe.1,hRe.2,hcore.1,hcore.2]

end Liu
