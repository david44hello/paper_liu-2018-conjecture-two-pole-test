module

public import Liu.GreenLinearization

@[expose] public section

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate Topology
namespace Liu

def reflectedPotential (ρ : ℂ → ℂ) (z : ℂ) : ℂ := ∫ w, (greenLog z w:ℂ)*ρ w ∂upperArea

def greenDifferential (ρ : ℂ → ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (∫ w, (((greenResolvent z w).re:ℝ):ℂ)*ρ w ∂upperArea) -
    Complex.imCLM.smulRight (∫ w, (((greenResolvent z w).im:ℝ):ℂ)*ρ w ∂upperArea)

theorem upperArea_ae_ne (z : ℂ) : ∀ᵐ w ∂upperArea, w≠z := by
  letI : NullSingletonClass area := ⟨fun x => by simp [area,Measure.smul_apply]⟩
  letI : NullSingletonClass upperArea := by unfold upperArea; infer_instance
  exact upperArea.ae_ne z

theorem resolvent_source_integrable {ρ : ℂ → ℂ} (hm : Measurable ρ) {K : ℝ} (hK : 0≤K)
    (hb : ∀ w ∈ upper, ‖ρ w‖≤K/(1+‖w‖)^2) {z : ℂ} (hz : 0≤z.im) :
    Integrable (fun w => (greenResolvent z w)*ρ w) upperArea ∧
    Integrable (fun w => (((greenResolvent z w).re:ℝ):ℂ)*ρ w) upperArea ∧
    Integrable (fun w => (((greenResolvent z w).im:ℝ):ℂ)*ρ w) upperArea := by
  obtain ⟨_,_,h⟩ := gradientWeight_integral
  have hi := (h z).1.const_mul (2*K)
  have m : Measurable (greenResolvent z) := by unfold greenResolvent; fun_prop
  have hdom : ∀ᵐ w ∂upperArea, ‖greenResolvent z w‖*‖ρ w‖ ≤ (2*K)*gradientWeight z w := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,upperArea_ae_ne z] with w hw hn
    apply (mul_le_mul (greenResolvent_bound hz hw hn.symm) (hb w hw) (norm_nonneg _) (by positivity)).trans
    calc
      _ = (2*K)*(‖z-w‖⁻¹/(1+‖w‖)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (gradientWeight_majorizes z w) (by positivity)
  refine ⟨hi.mono' (m.mul hm).aestronglyMeasurable (by simpa only [norm_mul] using hdom),?_,?_⟩
  · apply hi.mono' (by fun_prop)
    filter_upwards [hdom] with w hw
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (norm_nonneg _)).trans hw
  · apply hi.mono' (by fun_prop)
    filter_upwards [hdom] with w hw
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm _) (norm_nonneg _)).trans hw

theorem greenDifferential_apply {ρ : ℂ → ℂ} (hm : Measurable ρ) {K : ℝ} (hK : 0≤K)
    (hb : ∀ w ∈ upper, ‖ρ w‖≤K/(1+‖w‖)^2) {z : ℂ} (hz : 0≤z.im) (h : ℂ) :
    greenDifferential ρ z h = ∫ w, ((((h*greenResolvent z w).re):ℝ):ℂ)*ρ w ∂upperArea := by
  obtain ⟨_,hi,hj⟩ := resolvent_source_integrable hm hK hb hz
  simp only [greenDifferential,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply,Complex.imCLM_apply,Complex.real_smul]
  rw [←integral_const_mul,←integral_const_mul,←integral_sub (hi.const_mul (h.re:ℂ)) (hj.const_mul (h.im:ℂ))]
  apply integral_congr_ae
  filter_upwards with w
  simp only [Pi.sub_apply,Complex.mul_re,Complex.ofReal_sub,Complex.ofReal_mul]; ring

theorem greenDifferential_integrable_apply {ρ : ℂ → ℂ} (hm : Measurable ρ) {K : ℝ} (hK : 0≤K)
    (hb : ∀ w ∈ upper, ‖ρ w‖≤K/(1+‖w‖)^2) {z : ℂ} (hz : 0≤z.im) (h : ℂ) :
    Integrable (fun w => ((((h*greenResolvent z w).re):ℝ):ℂ)*ρ w) upperArea := by
  obtain ⟨_,hi,hj⟩ := resolvent_source_integrable hm hK hb hz
  apply ((hi.const_mul (h.re:ℂ)).sub (hj.const_mul (h.im:ℂ))).congr
  filter_upwards with w
  simp only [Pi.sub_apply,Complex.mul_re,Complex.ofReal_sub,Complex.ofReal_mul]; ring

end Liu
