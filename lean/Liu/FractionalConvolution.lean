import Liu.KernelIncrement
import Liu.CauchyTransform

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped Topology
namespace Liu

/-- Fractional Cauchy kernel against quadratic decay of the source. -/
def fractionalWeight (z w : ℂ) := ‖w-z‖^(-(7/4:ℝ))/(1+‖w‖)^2

private def singularPart : ℂ → ℝ :=
  (ball 0 1).indicator (fun s => ‖s‖^(-(7/4:ℝ)))

private def integrableTail (w : ℂ) := (1+‖w‖)^(-(5/2:ℝ))

private theorem product_decay {a b R : ℝ} (ha : 1≤a) (hb : 1≤b) (hR : 0≤R) (hab : R≤a+b) :
    R^(5/4:ℝ)*b^(-(7/4:ℝ))*a^(-(2:ℝ))≤
      4*(a^(-(5/2:ℝ))+b^(-(5/2:ℝ))) := by
  have hap := zero_lt_one.trans_le ha
  have hbp := zero_lt_one.trans_le hb
  have htwo : (2:ℝ)^(5/4:ℝ)≤4 :=
    (rpow_le_rpow_of_exponent_le (by norm_num : 1≤(2:ℝ)) (by norm_num : (5/4:ℝ)≤2)).trans_eq (by norm_num)
  rcases le_total a b with h | h
  · have h₁ := rpow_le_rpow hR (by linarith : R≤2*b) (by norm_num : (0:ℝ)≤5/4)
    rw [mul_rpow (by norm_num) hbp.le] at h₁
    have h₂ := h₁.trans (mul_le_mul_of_nonneg_right htwo (rpow_nonneg hbp.le _))
    have h₃ := mul_le_mul_of_nonneg_right h₂ (rpow_nonneg hbp.le (-(7/4:ℝ)))
    rw [mul_assoc 4,←rpow_add hbp,show (5/4:ℝ)+-(7/4)= -(1/2) by norm_num] at h₃
    have h₄ := rpow_le_rpow_of_nonpos hap h (by norm_num : -(1/2:ℝ)≤0)
    have h₅ := mul_le_mul_of_nonneg_right (h₃.trans (mul_le_mul_of_nonneg_left h₄ (by norm_num))) (rpow_nonneg hap.le (-(2:ℝ)))
    rw [mul_assoc 4,←rpow_add hap,show -(1/2:ℝ)+-2= -(5/2) by norm_num] at h₅
    linarith only [h₅,rpow_nonneg hbp.le (-(5/2:ℝ))]
  · have h₁ := rpow_le_rpow hR (by linarith : R≤2*a) (by norm_num : (0:ℝ)≤5/4)
    rw [mul_rpow (by norm_num) hap.le] at h₁
    have h₂ := h₁.trans (mul_le_mul_of_nonneg_right htwo (rpow_nonneg hap.le _))
    have h₃ := mul_le_mul_of_nonneg_right h₂ (rpow_nonneg hap.le (-(2:ℝ)))
    rw [mul_assoc 4,←rpow_add hap,show (5/4:ℝ)+-2= -(3/4) by norm_num] at h₃
    have h₄ := rpow_le_rpow_of_nonpos hbp h (by norm_num : -(3/4:ℝ)≤0)
    have h₅ := mul_le_mul_of_nonneg_right (h₃.trans (mul_le_mul_of_nonneg_left h₄ (by norm_num))) (rpow_nonneg hbp.le (-(7/4:ℝ)))
    rw [mul_assoc 4,←rpow_add hbp,show -(3/4:ℝ)+-(7/4)= -(5/2) by norm_num] at h₅
    linarith only [h₅,rpow_nonneg hap.le (-(5/2:ℝ))]

private theorem fractional_majorant (z w : ℂ) :
    (1+‖z‖)^(5/4:ℝ)*fractionalWeight z w ≤
      4*singularPart (w-z)+16*(integrableTail w+integrableTail (w-z)) := by
  let R := 1+‖z‖
  let a := 1+‖w‖
  let s := ‖w-z‖
  let b := 1+s
  have h0 : 0≤ s := norm_nonneg _
  have ha : 1≤a := by dsimp [a]; linarith [norm_nonneg w]
  have hb : 1≤b := by dsimp [b]; linarith
  have hap := zero_lt_one.trans_le ha
  have hbp := zero_lt_one.trans_le hb
  have hr : 0<R := by dsimp [R]; positivity
  have ht : R≤a+s := by
    have h := norm_sub_le_norm_sub_add_norm_sub z w 0
    simp only [sub_zero,norm_sub_rev z w] at h
    dsimp only [R,a,s]; linarith
  change R^(5/4:ℝ)*(s^(-(7/4:ℝ))/a^2)≤4*singularPart (w-z)+16*(a^(-(5/2:ℝ))+b^(-(5/2:ℝ)))
  by_cases h : s<1
  · have hmem : w-z∈ball (0:ℂ) 1 := by simpa only [mem_ball,dist_zero_right] using h
    rw [singularPart,indicator_of_mem hmem]
    have h₂ : (2:ℝ)^(5/4:ℝ)≤4 := (rpow_le_rpow_of_exponent_le (by norm_num : 1≤(2:ℝ)) (by norm_num : (5/4:ℝ)≤2)).trans_eq (by norm_num)
    have hR := rpow_le_rpow hr.le (by linarith : R≤2*a) (by norm_num : (0:ℝ)≤5/4)
    rw [mul_rpow (by norm_num) hap.le] at hR
    have hA := rpow_le_rpow_of_exponent_le ha (by norm_num : (5/4:ℝ)≤2)
    rw [rpow_two] at hA
    have H := mul_le_mul_of_nonneg_right (hR.trans (mul_le_mul h₂ hA (rpow_nonneg hap.le _) (by norm_num))) (div_nonneg (rpow_nonneg h0 (-(7/4:ℝ))) (sq_nonneg a))
    have he : 4*a^2*(s^(-(7/4:ℝ))/a^2)=4*s^(-(7/4:ℝ)) := by field_simp [hap.ne']
    rw [he] at H
    change _≤4*s^(-(7/4:ℝ))+_
    linarith only [H,rpow_nonneg hap.le (-(5/2:ℝ)),rpow_nonneg hbp.le (-(5/2:ℝ))]
  · have hs := zero_lt_one.trans_le (le_of_not_gt h)
    have h₂ : (2:ℝ)^(7/4:ℝ)≤4 := (rpow_le_rpow_of_exponent_le (by norm_num : 1≤(2:ℝ)) (by norm_num : (7/4:ℝ)≤2)).trans_eq (by norm_num)
    have hsmall := rpow_le_rpow_of_nonpos (half_pos hbp) (by dsimp [b]; linarith : b/2≤ s) (by norm_num : -(7/4:ℝ)≤0)
    rw [div_rpow hbp.le (by norm_num),rpow_neg (by norm_num : 0≤(2:ℝ)),div_inv_eq_mul] at hsmall
    have hweight := hsmall.trans (mul_le_mul_of_nonneg_left h₂ (rpow_nonneg hbp.le _))
    have hprod := product_decay ha hb hr.le (by dsimp [b]; linarith)
    have hpos : 0≤ singularPart (w-z) := indicator_nonneg (fun x _ => rpow_nonneg (norm_nonneg x) _) _
    rw [div_eq_mul_inv (s^(-(7/4:ℝ))) (a^2),←Real.rpow_two a,←rpow_neg hap.le]
    nlinarith only [hprod,hpos,mul_le_mul_of_nonneg_left hweight
      (mul_nonneg (rpow_nonneg hr.le (5/4:ℝ)) (rpow_nonneg hap.le (-(2:ℝ))))]

theorem fractional_convolution_bound :
    ∃ C≥0, ∀ z : ℂ, Integrable (fractionalWeight z) upperArea ∧
      (∫ w, fractionalWeight z w ∂upperArea) ≤ C/(1+‖z‖)^(5/4:ℝ) := by
  have hS : Integrable singularPart volume := by
    apply (integrable_indicator_iff isOpen_ball.measurableSet).mpr
    apply integrableOn_ball_of_norm_le_rpow (C:=1) (α:=(7/4:ℝ)) (by simp) (by norm_num)
    · exact ae_of_all _ fun w => by simp [abs_of_nonneg (rpow_nonneg (norm_nonneg w) (-(7/4:ℝ)))]
    · exact (by fun_prop : Measurable (fun w : ℂ => ‖w‖^(-(7/4:ℝ)))).aestronglyMeasurable
  have hT : Integrable integrableTail volume := integrable_one_add_norm (by norm_num)
  let C := 4*(∫ w, singularPart w)+32*(∫ w,integrableTail w)
  have hS0 w : 0≤ singularPart w := indicator_nonneg (fun x _ => rpow_nonneg (norm_nonneg x) _) _
  have hT0 w : 0≤ integrableTail w := rpow_nonneg (by positivity) _
  have hSI : 0≤∫ w, singularPart w := integral_nonneg fun w => hS0 w
  have hTI : 0≤∫ w, integrableTail w := integral_nonneg fun w => hT0 w
  refine ⟨(1/π)*C,mul_nonneg (by positivity) (by dsimp [C]; linarith only [hSI,hTI]),?_⟩
  intro z
  let F := fun w => (1+‖z‖)^(5/4:ℝ)*fractionalWeight z w
  let G := fun w => 4*singularPart (w-z)+16*(integrableTail w+integrableTail (w-z))
  have mp := measurePreserving_add_right (volume:Measure ℂ) (-z)
  have emb := (Homeomorph.addRight (-z)).measurableEmbedding
  have hS' : Integrable (fun w => singularPart (w-z)) volume := (mp.integrable_comp_emb emb).mpr hS
  have hT' : Integrable (fun w => integrableTail (w-z)) volume := (mp.integrable_comp_emb emb).mpr hT
  have hiG : Integrable G volume := (hS'.const_mul 4).add ((hT.add hT').const_mul 16)
  have hG : (∫ w, G w)=C := by
    have eS : (∫ w, singularPart (w-z))=∫ w,singularPart w := mp.integral_comp emb _
    have eT : (∫ w, integrableTail (w-z))=∫ w,integrableTail w := mp.integral_comp emb _
    dsimp only [G,C]
    erw [integral_add (hS'.const_mul 4) ((hT.add hT').const_mul 16),integral_const_mul,integral_const_mul,integral_add hT hT',eS,eT]; ring
  have hF0 w : 0≤F w := by dsimp [F,fractionalWeight]; positivity
  have hiF : Integrable F volume := hiG.mono' (show Measurable F by dsimp [F,fractionalWeight]; fun_prop).aestronglyMeasurable (ae_of_all _ fun w => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hF0 w)]; exact fractional_majorant z w)
  have hr : 0<(1+‖z‖)^(5/4:ℝ) := by positivity
  have hi : Integrable (fractionalWeight z) volume := by
    have H := hiF.const_mul ((1+‖z‖)^(5/4:ℝ))⁻¹
    simpa only [F,←mul_assoc,inv_mul_cancel₀ hr.ne',one_mul] using H
  refine ⟨(hi.smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).restrict,?_⟩
  have h := (setIntegral_le_integral hiF (ae_of_all _ hF0) (s:=upper)).trans
    ((integral_mono hiF hiG (fractional_majorant z)).trans_eq hG)
  dsimp only [F] at h
  rw [integral_const_mul] at h
  rw [upperArea,area,Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),smul_eq_mul]
  apply (le_div_iff₀ hr).mpr
  nlinarith only [mul_le_mul_of_nonneg_left h (by positivity : 0≤1/π)]

end Liu
