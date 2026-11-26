import Liu.FarFieldClaim
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology ComplexConjugate Interval
namespace Liu

private def exhaustionBox (R : ℝ) := Ioc (-R) R ×ˢ Ioc 0 R

private theorem rectangle_exhaust {g : ℂ → ℂ} (hg : Integrable g upperArea) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, ∫ y in (0:ℝ)..R, upper.indicator g ((x:ℂ)+(y:ℂ)*Complex.I))
      atTop (𝓝 (∫ w in upper, g w ∂volume)) := by
  classical
  let G := upper.indicator g
  let e := Complex.measurableEquivRealProd.symm
  let q := G ∘ e
  have hV : Integrable G volume := by
    apply (integrable_indicator_iff upper_open.measurableSet).mpr
    unfold upperArea area at hg
    rw [Measure.restrict_smul] at hg
    exact (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top).mp hg
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have hq : Integrable q (volume.prod volume) := by
    rw [←Measure.volume_eq_prod]
    exact (hp.integrable_comp_emb e.measurableEmbedding).mpr hV
  have heq : (∫ u, q u ∂volume.prod volume)=∫ z in upper, g z ∂volume := by
    rw [←Measure.volume_eq_prod,←integral_indicator upper_open.measurableSet]
    exact hp.integral_comp e.measurableEmbedding G
  have hmono : Monotone exhaustionBox := fun a b hab => Set.prod_mono (Ioc_subset_Ioc (neg_le_neg hab) hab) (Ioc_subset_Ioc_right hab)
  have hlim := tendsto_setIntegral_of_monotone (μ:=volume.prod volume) (s:=exhaustionBox)
    (fun _ => measurableSet_Ioc.prod measurableSet_Ioc) hmono (hq.integrableOn (s:=⋃ R, exhaustionBox R))
  have hzero : ∀ u : ℝ×ℝ, u∉⋃ R, exhaustionBox R → q u=0 := by
    intro u hu
    by_cases him : 0<u.2
    · exfalso
      apply hu
      refine mem_iUnion.mpr ⟨|u.1|+|u.2|+1,?_,him,?_⟩
      · constructor <;> linarith [le_abs_self u.1,neg_le_abs u.1,abs_nonneg u.2]
      · linarith [abs_nonneg u.1,le_abs_self u.2]
    · exact indicator_of_notMem (show e u∉upper from him) g
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,heq] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  rw [intervalIntegral.integral_of_le (by linarith : -R≤R)]
  simp_rw [intervalIntegral.integral_of_le hR]
  unfold exhaustionBox
  rw [setIntegral_prod q hq.integrableOn]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y _
  change upper.indicator g (⟨x,y⟩:ℂ)=_
  rw [Complex.mk_eq_add_mul_I]

/-- The upper half-plane Stokes identity with zero boundary data follows by rectangular
exhaustion when the boundary integrand is o(1/r) and its curl is integrable. -/
theorem upper_curl_integral_zero {F k : ℂ → ℂ}
    (hc : ContinuousOn F {w : ℂ | 0≤w.im}) (hd : DifferentiableOn ℝ F upper)
    (hcurl : ∀ w ∈ upper, Complex.I*fderiv ℝ F w 1-fderiv ℝ F w Complex.I=k w)
    (hbottom : ∀ x : ℝ, F (x:ℂ)=0) (hi : Integrable k upperArea)
    {b : ℝ → ℝ} (hlim : Tendsto (fun R => R*b R) atTop (𝓝 0))
    (hdec : ∀ᶠ R in atTop, ∀ z : ℂ, 0≤z.im → R≤‖z‖ → ‖F z‖≤b R) :
    ∫ w, k w ∂upperArea=0 := by
  classical
  let D := fun w : ℂ => if w∈upper then fderiv ℝ F w else 0
  have hD (w : ℂ) : Complex.I * D w 1 - D w Complex.I = upper.indicator k w := by
    by_cases hw : w∈upper
    · simpa only [D,if_pos hw,indicator_of_mem hw,smul_eq_mul] using hcurl w hw
    · simp [D,hw]
  have hV : Integrable (upper.indicator k) volume := by
    apply (integrable_indicator_iff upper_open.measurableSet).mpr
    unfold upperArea area at hi
    rw [Measure.restrict_smul] at hi
    exact (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top).mp hi
  let A := fun R : ℝ => ∫ x in (-R)..R, ∫ y in (0:ℝ)..R, upper.indicator k ((x:ℂ)+(y:ℂ)*Complex.I)
  have bound : ∀ᶠ R in atTop, ‖A R‖≤4*(R*b R) := by
    filter_upwards [eventually_gt_atTop (0:ℝ),hdec] with R hR hb
    let a : ℂ := ⟨-R,0⟩
    let c : ℂ := ⟨R,R⟩
    have hLR : -R≤R := by linarith
    have hrect := Complex.integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real F D a c
      (hc.mono (show [[a.re,c.re]] ×ℂ [[a.im,c.im]] ⊆ {w : ℂ | 0≤w.im} by
        intro w hw; have hh := hw.2; change w.im ∈ uIcc 0 R at hh; rw [uIcc_of_le hR.le] at hh; exact hh.1))
      (by intro w hw; have hh := hw.2.1
          change min (0:ℝ) R < w.im at hh
          rw [min_eq_left hR.le] at hh
          have hu : w∈upper := hh
          simpa only [D,if_pos hu] using (hd.differentiableAt (upper_open.mem_nhds hu)).hasFDerivAt)
      (by simp only [smul_eq_mul]; simp_rw [hD]; exact hV.integrableOn)
    simp only [a,c,hD,Complex.ofReal_zero,zero_mul,add_zero,hbottom,intervalIntegral.integral_zero,zero_sub,smul_eq_mul] at hrect
    let top := ∫ x in (-R)..R, F ((x:ℂ)+(R:ℂ)*Complex.I)
    let right := ∫ y in (0:ℝ)..R, F ((R:ℂ)+(y:ℂ)*Complex.I)
    let left := ∫ y in (0:ℝ)..R, F (((-R:ℝ):ℂ)+(y:ℂ)*Complex.I)
    have htop : ‖top‖≤b R*(2*R) := by
      apply (intervalIntegral.norm_integral_le_of_norm_le_const (C:=b R) (fun x _ => hb _ (by simpa using hR.le) (by
        simpa using Complex.im_le_norm ((x:ℂ)+(R:ℂ)*Complex.I)))).trans_eq
      rw [abs_of_nonneg (by linarith : 0≤R- -R)]; ring
    have edge (s : ℝ) (hs : |s|=R) : ‖∫ y in (0:ℝ)..R, F ((s:ℂ)+(y:ℂ)*Complex.I)‖≤b R*R := by
      apply (intervalIntegral.norm_integral_le_of_norm_le_const (C:=b R) (fun y hy => hb _ (by
        have h : y∈Ioc 0 R := (uIoc_of_le hR.le) ▸ hy
        simpa using h.1.le) (by simpa [hs] using Complex.abs_re_le_norm ((s:ℂ)+(y:ℂ)*Complex.I)))).trans_eq
      rw [sub_zero,abs_of_pos hR]
    have hr := edge R (abs_of_pos hR)
    have hl := edge (-R) (by rw [abs_neg,abs_of_pos hR])
    change -top+Complex.I*right-Complex.I*left=A R at hrect
    rw [←hrect]
    apply (norm_sub_le ..).trans
    have hadd := norm_add_le (-top) (Complex.I*right)
    simp only [norm_neg,norm_mul,Complex.norm_I,one_mul] at hadd ⊢
    change ‖right‖≤_ at hr
    change ‖left‖≤_ at hl
    nlinarith only [htop,hr,hl,hadd]
  have hzero : Tendsto A atTop (𝓝 0) := squeeze_zero_norm' bound (by simpa using hlim.const_mul 4)
  have he := tendsto_nhds_unique (rectangle_exhaust hi) hzero
  unfold upperArea area
  rw [Measure.restrict_smul,integral_smul_measure,he,smul_zero]

end Liu
