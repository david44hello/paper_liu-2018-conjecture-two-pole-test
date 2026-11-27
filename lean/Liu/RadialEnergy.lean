module

public import Liu.FinitePart
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

noncomputable section
open Set MeasureTheory Real
namespace Liu

/-- The angular factor π cancels the normalized area factor 1/π. -/
theorem upperArea_radial (f : ℝ → ℝ) :
    ∫ z : ℂ, f ‖z‖ ∂upperArea = ∫ r in Ioi (0:ℝ), r * f r := by
  classical
  let θ := Ioo (0:ℝ) π
  let θall := Ioo (-π) π
  have sub : θ ⊆ θall := Ioo_subset_Ioo (by linarith [pi_pos]) le_rfl
  have angle : ∫ t in θall, θ.indicator (fun _ => (1:ℝ)) t = π := by
    rw [setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr sub]
    simp [θ,Real.volume_real_Ioo_of_le pi_pos.le]
  unfold upperArea area
  rw [Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),
    ← integral_indicator upper_open.measurableSet,← Complex.integral_comp_polarCoord_symm,
    polarCoord_target]
  have step : (∫ v in Ioi (0:ℝ) ×ˢ θall,
      v.1 • upper.indicator (fun z : ℂ => f ‖z‖) (Complex.polarCoord.symm v)) =
      (∫ r in Ioi (0:ℝ), r*f r) * ∫ t in θall, θ.indicator (fun _ => (1:ℝ)) t := by
    rw [← setIntegral_prod_mul,Measure.volume_eq_prod]
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    rintro ⟨r,t⟩ ⟨hr,ht⟩
    change 0 < r at hr
    have him : (Complex.polarCoord.symm (r,t)).im = r * sin t := by simp [← Complex.ofReal_sin,← Complex.ofReal_cos]
    by_cases h : 0 < t
    · have hz : Complex.polarCoord.symm (r,t) ∈ upper := by
        change 0 < (Complex.polarCoord.symm (r,t)).im
        rw [him]; exact mul_pos hr (sin_pos_of_pos_of_lt_pi h ht.2)
      have ha : t ∈ θ := ⟨h,ht.2⟩
      simp only [indicator_of_mem hz,indicator_of_mem ha,Complex.norm_polarCoord_symm,abs_of_pos hr,smul_eq_mul,mul_one]
    · have hz : Complex.polarCoord.symm (r,t) ∉ upper := by
        change ¬0 < (Complex.polarCoord.symm (r,t)).im
        rw [him]; exact not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hr.le
          (sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt h) ht.1.le))
      have ha : t ∉ θ := fun he => h he.1
      simp only [indicator_of_notMem hz,indicator_of_notMem ha,smul_zero,mul_zero]
  rw [step,angle,smul_eq_mul]
  field_simp [pi_ne_zero]

def radialTail (q : ℝ) (z : ℂ) : ℝ :=
  if 1 < ‖z‖ then ‖z‖^(-q) else 0

theorem radialTail_integral {q : ℝ} (hq : 2 < q) :
    ∫ z, radialTail q z ∂upperArea = 1/(q-2) := by
  classical
  have h := upperArea_radial (fun r => if 1 < r then r^(-q) else 0)
  change (∫ z, (if 1 < ‖z‖ then ‖z‖^(-q) else 0) ∂upperArea) = _
  rw [h]
  calc
    _ = ∫ r in Ioi (0:ℝ), (Ioi (1:ℝ)).indicator (fun u => u^(1-q)) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      by_cases hh : 1 < r
      · simp only [if_pos hh,indicator_of_mem (show r ∈ Ioi (1:ℝ) from hh)]
        rw [sub_eq_add_neg,Real.rpow_add hr,Real.rpow_one]
      · simp [hh,Set.indicator_of_notMem (show r ∉ Ioi (1:ℝ) from hh)]
    _ = _ := by
      rw [setIntegral_indicator measurableSet_Ioi,inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num)),
        integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,one_rpow]
      rw [show 1-q+1 = -(q-2) by ring, neg_div_neg_eq]

end Liu
