module

public import Liu.EdgeKernelDifference

@[expose] public section

noncomputable section
open Set Real MeasureTheory
namespace Liu

/-- A translated source is integrated only above the observation height. -/
def edgeSlice (f : ℂ → ℝ) (u x Y : ℝ) : ℝ :=
  (Ioi u).indicator (fun t => edgeAverage x (t-u) (fun X => f ⟨X,t⟩)) Y

theorem edgeSlice_integral (f : ℂ → ℝ) (u x : ℝ) :
    (∫ Y, edgeSlice f u x Y) = depthPoissonReal u x f := by
  unfold edgeSlice depthPoissonReal edgeAverage
  rw [integral_indicator measurableSet_Ioi,integral_div]
  ring

private theorem slice_measurable {f : ℂ → ℝ} (hf : Measurable f) (u x : ℝ) :
    Measurable (edgeSlice f u x) := by
  have hmk : Measurable (fun p : ℝ×ℝ => (⟨p.2,p.1⟩:ℂ)) :=
    Complex.measurableEquivRealProd.symm.measurable.comp measurable_swap
  have hm : Measurable (fun p : ℝ×ℝ => poissonLine x (p.1-u) p.2*f ⟨p.2,p.1⟩) := by
    apply Measurable.mul _ (hf.comp hmk); unfold poissonLine; fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right'.measurable.div_const π).indicator measurableSet_Ioi

theorem edgeSlice_le {f : ℂ → ℝ} {M u x Y : ℝ} (hM : 0≤M)
    (hf : u<Y → ∀ X, |f ⟨X,Y⟩|≤M) : |edgeSlice f u x Y|≤M := by
  by_cases h : u<Y
  · rw [edgeSlice,indicator_of_mem (show Y∈Ioi u from h)]
    exact edgeAverage_bound _ (sub_pos.mpr h) (hf h)
  · simpa [edgeSlice,show Y∉Ioi u from h] using hM

theorem edgeSlice_integrable {f : ℂ → ℝ} (hf : Measurable f) {u C : ℝ} (hu : 0≤u) (hC : 0≤C)
    (hbd : ∀ z : ℂ, 0<z.im → |f z|≤C) (htail : ∀ z : ℂ, 1<z.im → |f z|≤C/z.im^2) (x : ℝ) :
    Integrable (edgeSlice f u x) := by
  let L := (Ioc (0:ℝ) 1).indicator (fun _ => C)
  let T := (Ioi (1:ℝ)).indicator (fun Y => C*Y^(-(2:ℝ)))
  have hi : Integrable L := (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have hj : Integrable T := (integrable_indicator_iff measurableSet_Ioi).mpr
    ((integrableOn_Ioi_rpow_of_lt (a:=(-2:ℝ)) (by norm_num) (by norm_num : (0:ℝ)<1)).const_mul C)
  apply (hi.add hj).mono' (slice_measurable hf u x).aestronglyMeasurable
  filter_upwards with Y
  rw [Real.norm_eq_abs]
  by_cases hy : 0<Y
  · by_cases h : Y≤1
    · simpa [L,T,hy,h] using edgeSlice_le (u:=u) (x:=x) hC (fun _ X => hbd ⟨X,Y⟩ hy)
    · have hy₁ : 1<Y := lt_of_not_ge h
      simpa [L,T,h,hy₁,rpow_neg hy.le,div_eq_mul_inv] using
        edgeSlice_le (u:=u) (x:=x) (show 0≤C/Y^2 by positivity) (fun _ X => htail ⟨X,Y⟩ hy₁)
  · have hyu : ¬u<Y := fun h => hy (hu.trans_lt h)
    have hy₁ : ¬1<Y := by linarith
    simp [edgeSlice,L,T,hy,hyu,hy₁]

/-- Integrate a change on the short interval, a reciprocal majorant on the
middle interval, and a square-integrable tail. -/
theorem log_modulus_integral {C h : ℝ} (hC : 0≤C) (hh : 0<h) (hh₁ : h≤1/4)
    {f g : ℝ → ℝ} (hfi : Integrable f) (hgi : Integrable g)
    (hzero : ∀ Y, Y≤0 → f Y-g Y=0)
    (hsmall : ∀ Y, 0<Y → |f Y-g Y|≤C/2)
    (hmid : ∀ Y, 2*h<Y → Y≤1 → |f Y-g Y|≤2*C*h/Y)
    (hfar : ∀ Y, 1<Y → |f Y-g Y|≤2*C*h/Y^2) :
    |(∫ Y, f Y)-(∫ Y, g Y)|≤4*C*h*(1+log (1/h)) := by
  let L := (Ioc 0 (2*h)).indicator (fun _ => C/2)
  let M := (Ioc h 1).indicator (fun Y => (2*C*h)*Y⁻¹)
  let T := (Ioi (1:ℝ)).indicator (fun Y => (2*C*h)*Y^(-(2:ℝ)))
  have h01 : h≤1 := by linarith
  have hL : Integrable L := (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  have hM : Integrable M := (integrable_indicator_iff measurableSet_Ioc).mpr
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le h01).mp
      (show IntervalIntegrable (fun Y : ℝ => Y⁻¹) volume h 1 by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le h01]
        exact continuousOn_id.inv₀ (fun x hx => (hh.trans_le hx.1).ne'))).const_mul _)
  have hT : Integrable T := (integrable_indicator_iff measurableSet_Ioi).mpr
    ((integrableOn_Ioi_rpow_of_lt (a:=(-2:ℝ)) (by norm_num) (by norm_num : (0:ℝ)<1)).const_mul _)
  have hm0 (Y : ℝ) : 0≤M Y := indicator_nonneg (fun (t:ℝ) ht => by
    have hpos := hh.trans ht.1; positivity) _
  have ht0 (Y : ℝ) : 0≤T Y := indicator_nonneg (fun (t:ℝ) (ht:t∈Ioi (1:ℝ)) => by
    have hpos : 0<t := lt_trans zero_lt_one ht; positivity) _
  have hl0 (Y : ℝ) : 0≤L Y := indicator_nonneg (fun _ _ => by positivity) _
  have hmajor (Y : ℝ) : |f Y-g Y|≤L Y+M Y+T Y := by
    by_cases hy : 0<Y
    · by_cases hs : Y≤2*h
      · have e : L Y=C/2 := indicator_of_mem (show Y∈Ioc 0 (2*h) from ⟨hy,hs⟩) _
        linarith [hsmall Y hy,hm0 Y,ht0 Y]
      · by_cases hm : Y≤1
        · have h2 := lt_of_not_ge hs
          have e : M Y=2*C*h/Y := by unfold M; rw [indicator_of_mem (show Y∈Ioc h 1 from ⟨by linarith,hm⟩),div_eq_mul_inv]
          linarith [hmid Y h2 hm,hl0 Y,ht0 Y]
        · have h1 := lt_of_not_ge hm
          have e : T Y=2*C*h/Y^2 := by unfold T; rw [indicator_of_mem (show Y∈Ioi (1:ℝ) from h1),rpow_neg hy.le,rpow_ofNat,div_eq_mul_inv]
          linarith [hfar Y h1,hl0 Y,hm0 Y]
    · rw [hzero Y (le_of_not_gt hy),abs_zero]
      linarith [hl0 Y,hm0 Y,ht0 Y]
  rw [←integral_sub hfi hgi,←Real.norm_eq_abs]
  have hiLM : Integrable (fun Y => L Y+M Y) := hL.add hM
  apply (norm_integral_le_of_norm_le (hiLM.add hT) (ae_of_all _ (fun Y => (Real.norm_eq_abs _).le.trans (hmajor Y)))).trans
  change (∫ Y, (L Y+M Y)+T Y)≤_
  rw [integral_add hiLM hT,integral_add hL hM]
  have eL : (∫ Y, L Y)=h*C := by
    unfold L
    rw [integral_indicator measurableSet_Ioc,setIntegral_const,Real.volume_real_Ioc_of_le (by linarith)]
    simp; ring
  have eM : (∫ Y, M Y)=(2*C*h)*log (1/h) := by
    unfold M
    rw [integral_indicator measurableSet_Ioc,integral_const_mul,←intervalIntegral.integral_of_le h01,integral_inv_of_pos hh zero_lt_one]
  have eT : (∫ Y, T Y)=2*C*h := by
    unfold T
    rw [integral_indicator measurableSet_Ioi,integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]; norm_num
  rw [eL,eM,eT]
  have hlog := log_nonneg ((one_le_div hh).mpr h01)
  nlinarith only [mul_nonneg hC hh.le,mul_nonneg (mul_nonneg hC hh.le) hlog]

end Liu
