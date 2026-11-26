import Liu.EdgeSourceRegions
import Liu.EdgeConvolution
import Liu.GreenRadialWeights

noncomputable section
open Set Real MeasureTheory
namespace Liu

/-- The common uniform-in-position bound for the real source in E.3(a). -/
theorem edge_real_source_uniform {s γ : ℝ} (hg : γ∈Icc 0 (π/2))
    (hc : 1/2≤cos γ) {z : ℂ} (hz : 0<z.im) :
    let μ := min (normalMass s) (1-normalMass s)
    |(crossSource (normalMass s) (direction γ) z).re|≤2048/μ := by
  let μ := min (normalMass s) (1-normalMass s)
  have hμ : 0<μ := lt_min (Certificate.normalMass_pos _) (by
    rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _)
  obtain ⟨h₁,h₂,hbulk,_⟩ := edge_source_separated_feet (s:=s) hg hc hz
  have hcmp : 512/μ≤2048/μ := div_le_div_of_nonneg_right (by norm_num) hμ.le
  by_cases h : ‖z‖<μ*cos γ/8
  · exact ((h₁ h).1).trans hcmp
  by_cases h' : ‖z-(cos γ:ℂ)‖<μ*cos γ/8
  · exact ((h₂ h').1).trans hcmp
  exact (Complex.abs_re_le_norm _).trans (hbulk (le_of_not_gt h) (le_of_not_gt h'))

private def heightEnvelope (M y : ℝ) : ℝ :=
  (Ioc (0:ℝ) 2).indicator (fun _ => M) y + (Ioi (2:ℝ)).indicator (fun t => t^(-(2:ℝ))) y

private theorem heightEnvelope_int (M : ℝ) :
    Integrable (heightEnvelope M) ∧ ∫ y, heightEnvelope M y = 2*M+1/2 := by
  have h₁ : Integrable ((Ioc (0:ℝ) 2).indicator (fun _ => M)) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have h₂ : Integrable ((Ioi (2:ℝ)).indicator (fun y => y^(-(2:ℝ)))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num))
  refine ⟨h₁.add h₂,?_⟩
  unfold heightEnvelope
  rw [integral_add h₁ h₂,integral_indicator measurableSet_Ioc,integral_indicator measurableSet_Ioi,
    integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
  norm_num [Real.rpow_neg_one,Real.volume_Ioc,ENNReal.toReal_ofReal]

private theorem poisson_slice_bound (x : ℝ) {y M : ℝ} (hy : 0<y) (f : ℝ → ℝ)
    (hf : ∀ X, |f X|≤M) : |∫ X, poissonLine x y X*f X|≤π*M := by
  have hI : Integrable (poissonLine x y) := Integrable.of_integral_ne_zero ((poissonLine_integral x hy) ▸ pi_ne_zero)
  rw [←Real.norm_eq_abs,←poissonLine_integral x hy,←integral_mul_const]
  apply norm_integral_le_of_norm_le (hI.mul_const M)
  filter_upwards with X
  have hP : 0≤poissonLine x y X := by unfold poissonLine; positivity
  simpa [Real.norm_eq_abs,abs_mul,abs_of_nonneg hP] using mul_le_mul_of_nonneg_left (hf X) hP

/-- A height-by-height Poisson estimate. The same expression defines the
trace at zero; the inner kernel is used only at strictly positive height. -/
theorem depthPoissonReal_uniform {M u : ℝ} (hu : 0≤u) (hM : 0≤M) (f : ℂ → ℝ)
    (hbd : ∀ z : ℂ, 0<z.im → |f z|≤M)
    (hfar : ∀ z : ℂ, 0<z.im → 2≤‖z‖ → |f z|≤4/‖z‖^4) (x : ℝ) :
    |depthPoissonReal u x f|≤2*M+1/2 := by
  let G := heightEnvelope M
  obtain ⟨hI,hval⟩ := heightEnvelope_int M
  have hG (y : ℝ) : 0≤G y := by
    unfold G heightEnvelope
    apply add_nonneg (indicator_nonneg (fun _ _ => hM) _)
    exact indicator_nonneg (fun y hy => rpow_nonneg (le_trans (by norm_num) (le_of_lt hy)) _) _
  have hbound (Y : ℝ) (hY : u<Y) (X : ℝ) : |f ⟨X,Y⟩|≤G Y := by
    have hy := hu.trans_lt hY
    by_cases ht : Y≤2
    · simpa [G,heightEnvelope,hy,ht] using hbd ⟨X,Y⟩ hy
    · have h2 : 2<Y := lt_of_not_ge ht
      have hr := Complex.im_le_norm (⟨X,Y⟩:ℂ)
      change Y≤‖(⟨X,Y⟩:ℂ)‖ at hr
      have hn := hy.trans_le hr
      have hcmp : 4/‖(⟨X,Y⟩:ℂ)‖^4≤1/Y^2 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith only [pow_le_pow_left₀ hy.le hr 4,
          mul_le_mul_of_nonneg_right (show 4≤Y^2 by nlinarith [sq_nonneg (Y-2)]) (sq_nonneg Y)]
      exact (hfar _ hy (h2.le.trans hr)).trans (by simpa [G,heightEnvelope,h2,ht,rpow_neg hy.le,one_div] using hcmp)
  have hline (Y : ℝ) (hY : u<Y) := poisson_slice_bound x (sub_pos.mpr hY) _ (hbound Y hY)
  have hnorm := norm_integral_le_of_norm_le (f:=fun Y : ℝ => ∫ X, poissonLine x (Y-u) X*f ⟨X,Y⟩)
    (hI.const_mul π).integrableOn ((ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=u))).mono
      fun Y hY => (Real.norm_eq_abs _).le.trans (hline Y hY))
  have hle := setIntegral_le_integral (μ:=volume) (s:=Ioi u) hI (ae_of_all _ hG)
  rw [integral_const_mul] at hnorm
  unfold depthPoissonReal
  rw [abs_mul,abs_of_pos (by positivity : 0<(1:ℝ)/π),←Real.norm_eq_abs]
  calc
    _ ≤ (1/π)*(π*∫ Y in Ioi u, G Y) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = ∫ Y in Ioi u, G Y := by field_simp
    _ ≤ _ := hle.trans_eq hval

end Liu
