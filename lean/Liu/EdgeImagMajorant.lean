import Liu.EdgeHeightCost

noncomputable section
open Set Real MeasureTheory
namespace Liu

private def footWeight (r : ℝ) := if r≤4 then r^(-(3/2:ℝ)) else 0

private theorem footWeight_mass (x : ℝ) :
    Integrable (fun z : ℂ => footWeight ‖z-(x:ℂ)‖) upperArea ∧
    (∫ z : ℂ, footWeight ‖z-(x:ℂ)‖ ∂upperArea)≤4 := by
  apply translated_radial_majorant (by norm_num) _ _ (by simp)
  · intro r hr; unfold footWeight; split <;> positivity
  · have he (r : ℝ) (hr : r∈Ioi (0:ℝ)) : r*footWeight r =
        (Ioc (0:ℝ) 4).indicator (fun t => t^(-(1/2:ℝ))) r := by
      by_cases h : r≤4
      · rw [footWeight,if_pos h,indicator_of_mem (show r∈Ioc _ _ from ⟨hr,h⟩)]
        conv_lhs => lhs; rw [←rpow_one r]
        rw [←rpow_add hr]; norm_num
      · simp [footWeight,h,show r∉Ioc (0:ℝ) 4 from fun e => h e.2]
    rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr Ioc_subset_Ioi_self,←intervalIntegral.integral_of_le (by norm_num),
      integral_rpow (Or.inl (by norm_num))]
    norm_num [←sqrt_eq_rpow]

private theorem weighted_foot {f K r Y : ℝ} (hK : 0≤K) (hY : 0<Y) (hYr : Y≤r) (hr : r≤4)
    (hf : |f|≤K/r) : f^2*edgeHeightCost Y ≤ K^2*footWeight r := by
  have hr' := hY.trans_le hYr
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hf 2
  rw [sq_abs,div_pow] at hsq
  have he : sqrt r/r^2=r^(-(3/2:ℝ)) := by
    rw [show -(3/2:ℝ)=(1/2:ℝ)-2 by norm_num,rpow_sub hr',rpow_ofNat,sqrt_eq_rpow]
  calc
    _ ≤ (K^2/r^2)*sqrt r := by
      rw [edgeHeightCost,if_neg hY.not_ge,if_pos (hYr.trans hr)]
      exact mul_le_mul hsq (sqrt_le_sqrt hYr) (sqrt_nonneg _) (by positivity)
    _ = _ := by rw [footWeight,if_pos hr,←he]; ring

private theorem weighted_far {f r Y : ℝ} (hY : 0<Y) (hYr : Y≤r) (hr : 4<r)
    (hf : |f|≤4/r^4) : f^2*edgeHeightCost Y ≤ 16*radialInvTail 6 4 r := by
  have hr₀ := hY.trans_le hYr
  have hB : edgeHeightCost Y≤r^2 := by
    unfold edgeHeightCost; rw [if_neg hY.not_ge]
    split_ifs with h
    · have hs := sqrt_le_sqrt h
      norm_num at hs
      nlinarith [sq_nonneg (r-4)]
    · exact pow_le_pow_left₀ hY.le hYr 2
  have hs := pow_le_pow_left₀ (abs_nonneg _) hf 2
  rw [sq_abs] at hs
  calc
    _ ≤ (4/r^4)^2*r^2 := mul_le_mul hs hB (edgeHeightCost_pos _).le (sq_nonneg _)
    _ = _ := by
      rw [radialInvTail,indicator_of_mem (show r∈Ioi (4:ℝ) from hr)]
      field_simp [hr₀.ne'] <;> ring

/-- Integration of the two near-foot majorants, the bounded part of the
radius-four half-disc and the inverse-fourth-power exterior tail. -/
theorem edge_imag_weighted_area {f : ℂ → ℝ} (hf : Measurable f) (x : ℝ)
    {K₁ K₂ M : ℝ} (h₁ : 0≤K₁) (h₂ : 0≤K₂) (hM : 0≤M)
    (hcore : ∀ z : ℂ, 0<z.im → ‖z‖≤4 →
      |f z|≤K₁/‖z‖ ∨ (‖z-(x:ℂ)‖≤4 ∧ |f z|≤K₂/‖z-(x:ℂ)‖) ∨ |f z|≤M)
    (hfar : ∀ z : ℂ, 0<z.im → 4<‖z‖ → |f z|≤4/‖z‖^4) :
    let F := fun z => f z^2*edgeHeightCost z.im
    Integrable F upperArea ∧ (∫ z, F z ∂upperArea)≤4*K₁^2+4*K₂^2+16*M^2+1 := by
  obtain ⟨hA,hAv⟩ := footWeight_mass 0
  simp only [Complex.ofReal_zero,sub_zero] at hA hAv
  obtain ⟨hB,hBv⟩ := footWeight_mass x
  obtain ⟨hD,hDv⟩ := radialDisc_majorant (w:=0) (by simp) (R:=4) (by norm_num)
  obtain ⟨hT,hTv⟩ := radialInvTail_majorant (w:=0) (by simp) (b:=4) (by norm_num) (k:=6) (by decide)
  simp only [sub_zero] at hD hDv hT hTv
  norm_num [Real.rpow_neg (by norm_num : (0:ℝ)≤4)] at hTv
  let G := fun z : ℂ => K₁^2*footWeight ‖z‖ + K₂^2*footWeight ‖z-(x:ℂ)‖ +
    (2*M^2)*radialDisc 4 ‖z‖ + 16*radialInvTail 6 4 ‖z‖
  have hI : Integrable G upperArea :=
    (((hA.const_mul _).add (hB.const_mul _)).add (hD.const_mul _)).add (hT.const_mul _)
  have hfoot (r : ℝ) (hr : 0≤r) : 0≤footWeight r := by unfold footWeight; split <;> positivity
  have hpt (z : ℂ) (hz : 0<z.im) : f z^2*edgeHeightCost z.im≤G z := by
    have ha := mul_nonneg (sq_nonneg K₁) (hfoot ‖z‖ (norm_nonneg _))
    have hb := mul_nonneg (sq_nonneg K₂) (hfoot ‖z-(x:ℂ)‖ (norm_nonneg _))
    have hd : 0≤radialDisc 4 ‖z‖ := by unfold radialDisc; split <;> norm_num
    have ht : 0≤radialInvTail 6 4 ‖z‖ := indicator_nonneg (fun (r:ℝ) _ => (by positivity : (0:ℝ)≤(r^6)⁻¹)) _
    have hy := Complex.im_le_norm z
    have hyx : z.im≤‖z-(x:ℂ)‖ := by simpa using Complex.im_le_norm (z-(x:ℂ))
    unfold G
    by_cases hr : ‖z‖≤4
    · have hDn : radialDisc 4 ‖z‖=1 := if_pos hr
      rcases hcore z hz hr with h|⟨hrx,h⟩|h
      · linarith [weighted_foot h₁ hz hy hr h,mul_nonneg (sq_nonneg M) hd]
      · linarith [weighted_foot h₂ hz hyx hrx h,mul_nonneg (sq_nonneg M) hd]
      · have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
        rw [sq_abs] at hs
        have hh : edgeHeightCost z.im≤2 := by
          rw [edgeHeightCost,if_neg hz.not_ge,if_pos (hy.trans hr)]
          calc
            _ ≤ sqrt 4 := sqrt_le_sqrt (hy.trans hr)
            _ = _ := by norm_num
        rw [hDn,mul_one]
        linarith [mul_le_mul hs hh (edgeHeightCost_pos _).le (sq_nonneg M)]
    · linarith [weighted_far hz hy (lt_of_not_ge hr) (hfar z hz (lt_of_not_ge hr)),mul_nonneg (sq_nonneg M) hd]
  let F := fun z : ℂ => f z^2*edgeHeightCost z.im
  have hFm : Measurable F := (hf.pow_const 2).mul (edgeHeightCost_measurable.comp Complex.measurable_im)
  have hle : F≤ᵐ[upperArea] G := (ae_restrict_mem (μ:=area) upper_open.measurableSet).mono hpt
  have hi := hI.mono' hFm.aestronglyMeasurable (hle.mono (fun z hz => by
    rwa [Real.norm_of_nonneg (show 0≤F z from mul_nonneg (sq_nonneg _) (edgeHeightCost_pos _).le)]))
  refine ⟨hi,(integral_mono_ae hi hI hle).trans ?_⟩
  unfold G
  have hiAB : Integrable (fun z : ℂ => K₁^2*footWeight ‖z‖+K₂^2*footWeight ‖z-(x:ℂ)‖) upperArea :=
    (hA.const_mul _).add (hB.const_mul _)
  have hiABD : Integrable (fun z : ℂ => K₁^2*footWeight ‖z‖+K₂^2*footWeight ‖z-(x:ℂ)‖+
      (2*M^2)*radialDisc 4 ‖z‖) upperArea := hiAB.add (hD.const_mul _)
  rw [integral_add hiABD (hT.const_mul 16),integral_add hiAB (hD.const_mul (2*M^2)),
    integral_add (hA.const_mul (K₁^2)) (hB.const_mul (K₂^2))]
  simp only [integral_const_mul]
  nlinarith only [mul_le_mul_of_nonneg_left hAv (sq_nonneg K₁),mul_le_mul_of_nonneg_left hBv (sq_nonneg K₂),
    mul_le_mul_of_nonneg_left hDv (sq_nonneg M),hTv]

end Liu
