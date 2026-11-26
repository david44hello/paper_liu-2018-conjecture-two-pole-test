import Liu.ReciprocalSource

noncomputable section
open Set Real MeasureTheory Metric
open scoped ComplexConjugate Topology
namespace Liu

def partnerTrace (a : ℝ) (q w : ℂ) (x : ℝ) : ℂ :=
  ∫ z, ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*topRho a q w (z+Complex.I) ∂upperArea

private theorem unit_shift_lower {z : ℂ} (hz : 0≤z.im) : 1≤‖z+Complex.I‖ :=
  (show 1≤(z+Complex.I).im by simp only [Complex.add_im,Complex.I_im]; linarith).trans (Complex.im_le_norm _)

private theorem partner_trace_bound {a r : ℝ} (ha : 0≤a) (ha₁ : a≤1) (hr : r<1)
    {q w : ℂ} (hq : ‖q‖=1) (hw : ‖w‖≤r) (x : ℝ) :
    let K := (1+r)/(1-r)
    let J := K*K*(1+1/(1-r)^2)
    ∀ᵐ z ∂upperArea, ‖((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*topRho a q w (z+Complex.I)‖ ≤
      J*isolatedDensity 1 (-Complex.I) x z := by
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
  have hz₀ : 0<z.im := hz
  have h := (top_rational_bounds ha ha₁ hr hq (unit_shift_lower hz₀.le) hw).2
  have hp : 0≤z.im/‖z-(x:ℂ)‖^2 := by positivity
  rw [norm_mul,Complex.norm_of_nonneg hp,isolatedDensity,sub_neg_eq_add]
  exact (mul_le_mul_of_nonneg_left h hp).trans_eq (by ring)

theorem partnerTrace_differentiable {a : ℝ} (ha : 0≤a) (ha₁ : a≤1) {q : ℂ} (hq : ‖q‖=1)
    (x : ℝ) : DifferentiableOn ℂ (fun w => partnerTrace a q w x) (ball 0 1) := by
  apply differentiableOn_disc_integral upperArea
  · intro w
    exact (show Measurable (fun z : ℂ => ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*topRho a q w (z+Complex.I)) by
      unfold topRho topFactor topDerivFactor; fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    exact (top_value_rho_differentiable ha ha₁ hq (unit_shift_lower (le_of_lt hz))).2.const_mul _
  · intro r hr h₁
    let K := (1+r)/(1-r)
    let J := K*K*(1+1/(1-r)^2)
    refine ⟨fun z => J*isolatedDensity 1 (-Complex.I) x z,
      (isolatedDensity_integral zero_lt_one (by simp : (-Complex.I).im<0) x).1.const_mul J,?_⟩
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    intro w hw
    have hz₀ : 0<z.im := hz
    have h := (top_rational_bounds ha ha₁ h₁ hq (unit_shift_lower hz₀.le) hw).2
    have hp : 0≤z.im/‖z-(x:ℂ)‖^2 := by positivity
    rw [norm_mul,Complex.norm_of_nonneg hp,isolatedDensity,sub_neg_eq_add]
    exact (mul_le_mul_of_nonneg_left h hp).trans_eq (by dsimp [J,K]; ring)

theorem partnerTrace_majorant {a r : ℝ} (ha : 0≤a) (ha₁ : a≤1) (hr : r<1)
    {q w : ℂ} (hq : ‖q‖=1) (hw : ‖w‖≤r) (x : ℝ) :
    let K := (1+r)/(1-r)
    ‖partnerTrace a q w x‖ ≤ (K*K*(1+1/(1-r)^2))*isolatedTrace 0 1 x := by
  let K := (1+r)/(1-r)
  let J := K*K*(1+1/(1-r)^2)
  obtain ⟨hi,he⟩ := isolatedDensity_integral zero_lt_one (by simp : (-Complex.I).im<0) x
  apply (norm_integral_le_of_norm_le (hi.const_mul J) (partner_trace_bound ha ha₁ hr hq hw x)).trans_eq
  rw [integral_const_mul,he]; simp [J,K]

theorem partnerTrace_actual {s γ v : ℝ} (hg : γ∈Icc 0 π) (hv : 0≤v) (hv₁ : v<1) (x : ℝ) :
    field (unitDepthSum s γ v) x = -partnerTrace (normalMass s) (direction γ) v x := by
  have hf := (unitDepthPair s γ v hg hv).toPick.field_on_boundary x
  rw [unitDepthPair_value] at hf
  rw [hf,poissonTrace,partnerTrace]
  let K := fun z : ℂ => ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*topRho (normalMass s) (direction γ) v (z+Complex.I)
  have he : (fun z : ℂ => ((2*z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*source (unitDepthSum s γ v) z) =ᵐ[upperArea]
      fun z => Complex.I*K z := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    rw [unitDepth_source_partner (le_of_lt hz) (by rwa [abs_of_nonneg hv])]
    dsimp [K]; push_cast; ring
  change Complex.I*(∫ z, _ ∂upperArea)= -(∫ z, K z ∂upperArea)
  rw [integral_congr_ae he,integral_const_mul,←mul_assoc,Complex.I_mul_I,neg_one_mul]

end Liu
