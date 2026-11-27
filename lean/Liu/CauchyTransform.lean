module

public import Liu.GreenInterior

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter
open scoped ComplexConjugate Topology
namespace Liu

/-- Cauchy transform of a density on the upper half-plane, evaluated everywhere. -/
def cauchyTransform (f : ℂ → ℂ) (x : ℂ) : ℂ :=
  ∫ w, f w/(x-w) ∂upperArea

structure QuadraticDecay (f : ℂ → ℂ) : Prop where
  measurable : Measurable f
  bound : ∃ K ≥ 0, ∀ w ∈ upper, ‖f w‖ ≤ K/(1+‖w‖)^2

theorem QuadraticDecay.conjugate {f : ℂ → ℂ} (hf : QuadraticDecay f) :
    QuadraticDecay (fun w => conj (f w)) := by
  obtain ⟨K,hK,h⟩ := hf.bound
  exact ⟨Complex.continuous_conj.measurable.comp hf.measurable,K,hK,fun w hw => by simpa using h w hw⟩

theorem cauchyTransform_integrable {f : ℂ → ℂ} (hf : QuadraticDecay f) (x : ℂ) :
    Integrable (fun w => f w/(x-w)) upperArea := by
  obtain ⟨K,hK,h⟩ := hf.bound
  obtain ⟨_,_,hgrad⟩ := gradientWeight_integral
  have hm := hf.measurable
  have hme : Measurable (fun w => f w/(x-w)) := by fun_prop
  apply ((hgrad x).1.const_mul K).mono' hme.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
  rw [norm_div]
  apply (div_le_div_of_nonneg_right (h w hw) (norm_nonneg _)).trans
  calc
    _ = K*(‖x-w‖⁻¹/(1+‖w‖)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (gradientWeight_majorizes x w) hK

theorem cauchyTransform_continuous {f : ℂ → ℂ} (hf : QuadraticDecay f) : Continuous (cauchyTransform f) := by
  obtain ⟨K,hK,h⟩ := hf.bound
  obtain ⟨B,hB,hgrad⟩ := gradientWeight_integral
  let A := ∫ w, localInverse 0 w
  have hA : 0≤A := integral_nonneg fun w => indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _
  let C := 8*K*(1/π)*A+2*K*B
  rw [continuous_iff_continuousAt]
  intro z
  change Tendsto (cauchyTransform f) (𝓝 z) (𝓝 (cauchyTransform f z))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have ht : Tendsto (fun x : ℂ => ‖x-z‖) (𝓝 z) (𝓝 0) := by
    simpa using (continuous_id.sub (continuous_const (y:=z))).norm.tendsto z
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ (by
    simpa using (continuous_sqrt.continuousAt.tendsto.comp ht).const_mul C)
  filter_upwards [ht.eventually_lt_const (by norm_num : (0:ℝ)<1/4)] with x hs
  by_cases eq : x=z
  · simp [eq]
  let l := ‖x-z‖
  let δ := sqrt l
  let r := 4*δ
  have hl : 0<l := norm_pos_iff.mpr (sub_ne_zero.mpr eq)
  have hp : 0<δ := sqrt_pos.mpr hl
  have hr : 0<r := by dsimp [r]; positivity
  have hδ : δ^2=l := sq_sqrt hl.le
  have hthin : l≤δ/2 := by
    have hh : δ≤1/2 := by change l<1/4 at hs; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hh hp.le]
  let n := fun w => (K/r)*(scaledWeight r x w+scaledWeight r z w)
  let g := fun w => (2*l*K/δ)*gradientWeight z w
  obtain ⟨hix,hux⟩ := scaledWeight_estimate hr x
  obtain ⟨hiz,huz⟩ := scaledWeight_estimate hr z
  have hi : Integrable n upperArea := (hix.add hiz).const_mul _
  have hj : Integrable g upperArea := (hgrad z).1.const_mul _
  have hb : ∀ᵐ w ∂upperArea, ‖f w/(x-w)-f w/(z-w)‖ ≤ n w+g w := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,upperArea_ae_ne x,upperArea_ae_ne z] with w hw hwx hwz
    have hi0 (v : ℂ) : 0 ≤ scaledWeight r v w := by
      unfold scaledWeight localInverse; apply indicator_nonneg; exact fun _ _ => by positivity
    have hn0 : 0≤n w := by have := hi0 x; have := hi0 z; dsimp only [n]; positivity
    have hg0 : 0≤g w := by
      have hg := (by positivity : 0≤‖z-w‖⁻¹/(1+‖w‖)^2).trans (gradientWeight_majorizes z w)
      dsimp only [g]; positivity
    by_cases near : ‖z-w‖ < δ
    · apply le_trans _ (le_add_of_nonneg_right hg0)
      have hx : ‖x-w‖<r/2 := by
        have h := norm_sub_le_norm_sub_add_norm_sub x z w
        change ‖x-w‖ ≤ l+‖z-w‖ at h; dsimp [r]; linarith
      have hz : ‖z-w‖<r/2 := by dsimp [r]; linarith
      apply (norm_sub_le ..).trans
      rw [norm_div,norm_div]
      have hK' := (h w hw).trans (div_le_self hK (by nlinarith [norm_nonneg w,sq_nonneg ‖w‖]))
      apply (add_le_add (div_le_div_of_nonneg_right hK' (norm_nonneg _)) (div_le_div_of_nonneg_right hK' (norm_nonneg _))).trans_eq
      simp only [n,scaledWeight,scaled_inverse_near hr hx,scaled_inverse_near hr hz]
      field_simp [hr.ne'] <;> ring
    · apply le_trans _ (le_add_of_nonneg_left hn0)
      have hx : x-w≠0 := sub_ne_zero.mpr hwx.symm
      have hz : z-w≠0 := sub_ne_zero.mpr hwz.symm
      have hdist : δ/2 ≤ ‖x-w‖ := by
        have h := norm_sub_le_norm_sub_add_norm_sub z x w
        rw [norm_sub_rev z x] at h
        change ‖z-w‖ ≤ l+‖x-w‖ at h; linarith [le_of_not_gt near]
      have eqn : f w/(x-w)-f w/(z-w) = (z-x)*f w/((x-w)*(z-w)) := by field_simp [hx,hz]; ring
      rw [eqn,norm_div,norm_mul,norm_mul,norm_sub_rev z x]
      calc
        _ = (l*‖x-w‖⁻¹)*(‖f w‖*‖z-w‖⁻¹) := by dsimp only [l]; rw [div_eq_mul_inv,mul_inv_rev]; ring
        _ ≤ (l*(δ/2)⁻¹)*((K/(1+‖w‖)^2)*‖z-w‖⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (inv_anti₀ (half_pos hp) hdist) hl.le)
            (mul_le_mul_of_nonneg_right (h w hw) (by positivity)) (by positivity) (by positivity)
        _ = (2*l*K/δ)*(‖z-w‖⁻¹/(1+‖w‖)^2) := by rw [inv_div]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (gradientWeight_majorizes z w) (by positivity)
  have H := norm_integral_le_of_norm_le (hi.add hj) hb
  simp only [Pi.add_apply,integral_add hi hj,integral_sub (cauchyTransform_integrable hf x) (cauchyTransform_integrable hf z)] at H
  apply H.trans
  simp only [n,g,integral_const_mul,integral_add hix hiz]
  apply (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hux huz) (by positivity : 0≤K/r))
    (mul_le_mul_of_nonneg_left (hgrad z).2 (by positivity : 0≤2*l*K/δ))).trans_eq
  change (K/r)*((1/π)*(r^2*A)+(1/π)*(r^2*A))+(2*l*K/δ)*B=C*δ
  dsimp only [C,r]; rw [←hδ]; field_simp [hp.ne',pi_ne_zero] <;> ring

end Liu
