module

public import Liu.SupercriticalProjection
public import Liu.SourceTailComparison

@[expose] public section

noncomputable section
open Set MeasureTheory Filter Real
open scoped ComplexConjugate Topology
namespace Liu

/-- On the open half-plane an L² field of zero projection is determined
pointwise by its classical antiholomorphic derivative and its continuity. -/
theorem SupercriticalSource.identify_field {f V : ℂ → ℂ} {t : ℝ} (hf : SupercriticalSource f t)
    (df : DifferentiableOn ℝ f upper) (hV : MemLp V 2 upperArea) (dV : DifferentiableOn ℝ V upper)
    (hsol : EqOn (dbar V) f upper) (hp : project (asL2 V)=0) : EqOn V (canonicalField f) upper := by
  have he := hf.residual_eq_field df hV dV hsol
  rw [hp,sub_zero] at he
  have hF := hf.field_memLp
  simp only [asL2,dif_pos hV,dif_pos hF] at he
  have hae : V =ᵐ[upperArea] canonicalField f := hV.coeFn_toLp.symm.trans (he ▸ hF.coeFn_toLp)
  unfold upperArea area at hae
  rw [Measure.restrict_smul] at hae
  have hv := (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0<1/π))).mp hae
  exact Measure.eqOn_open_of_ae_eq hv upper_open dV.continuousOn (canonicalField_continuous hf.green.quadratic).continuousOn

/-- A single constant controls the canonical field of every cubic remainder
with the same pointwise envelope. -/
theorem canonicalField_uniform_cubic_error {K : ℝ} (hK : 0≤K) :
    ∃ C ≥ 0, ∀ (f : ℂ → ℂ), Measurable f →
      (∀ w∈upper, ‖f w‖≤K/(1+‖w‖)^3) →
      ∀ z : ℂ, 0≤z.im → 1<‖z‖ → ‖canonicalField f z‖≤C*(1+log ‖z‖)/‖z‖^2 := by
  let major := fun w : ℂ => ((K/(1+‖w‖)^3:ℝ):ℂ)
  have hm : Measurable major := by unfold major; fun_prop
  have hmnorm (w : ℂ) : ‖major w‖=K/(1+‖w‖)^3 := Complex.norm_of_nonneg (by positivity)
  have hb (w : ℂ) (hw : w∈upper) : ‖major w‖≤K/(‖w‖^2*(1+‖w‖)) := by
    rw [hmnorm]
    have hp : 0<‖w‖ := (show 0<w.im from hw).trans_le (Complex.im_le_norm w)
    apply div_le_div_of_nonneg_left hK (by positivity)
    nlinarith [sq_nonneg ‖w‖]
  obtain ⟨C,hC,h⟩ := greenResolvent_radial_error hm hK hb
  refine ⟨C,hC,?_⟩
  intro f hf hsrc z hz hr
  have hgreen := GreenSource.of_decay (by norm_num : (2:ℝ)<3) hK hf (by simpa only [rpow_ofNat] using hsrc)
  obtain ⟨B,hB,hq⟩ := hgreen.decay
  have hi := (resolvent_source_integrable hf hB hq hz).1
  rw [canonicalField_eq_integral hgreen.quadratic,norm_neg]
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono_ae hi.norm (h z hz hr).1.norm ?_).trans (h z hz hr).2
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
  simp only [norm_mul,hmnorm]
  exact mul_le_mul_of_nonneg_left (hsrc w hw) (norm_nonneg _)

end Liu
