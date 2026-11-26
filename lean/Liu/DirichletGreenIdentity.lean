import Liu.DirichletDerivatives

noncomputable section
open Set Filter MeasureTheory Real Complex
open scoped Topology ComplexConjugate ContDiff
namespace Liu

theorem dirPart_compact {V : ℂ → ℂ} (h : HasCompactSupport V) (v : ℂ) :
    HasCompactSupport (dirPart v V) := h.of_isClosed_subset (isClosed_tsupport _) (dirPart_support v V)

theorem dirPart_conj {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper) {z : ℂ} (hz : z∈closedUpper) (v : ℂ) :
    dirPart v (fun w => conj (V w)) z=conj (dirPart v V z) := by
  have H := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasFDerivWithinAt z
    ((h.differentiableOn (by simp) z hz).hasFDerivWithinAt)
  change (fderivWithin ℝ (Complex.conjCLE.toContinuousLinearMap ∘ V) closedUpper z) v=_
  rw [H.fderivWithin (closedUpper_uniqueDiff z hz)]; rfl

private theorem dir_curl_zero {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper)
    (hc : HasCompactSupport V) (hb : ∀ x : ℝ, V x=0) :
    I*(∫ z, dirPart 1 V z ∂upperArea) - (∫ z, dirPart I V z ∂upperArea)=0 := by
  have hi (v : ℂ) := closed_integrable_compact (dirPart_smooth h v).continuousOn (dirPart_compact hc v)
  have hd : DifferentiableOn ℝ V upper := (h.differentiableOn (by simp)).mono (fun z h => (show 0<z.im from h).le)
  obtain ⟨R,_,hR⟩ := hc.exists_pos_le_norm
  have H := upper_curl_integral_zero h.continuousOn hd
    (k:=fun z => I*dirPart 1 V z-dirPart I V z)
    (fun z hz => by simp only [dirPart_inside _ _ hz]) hb (((hi 1).const_mul I).sub (hi I))
    (b:=fun _ => 0) (by simp) (by filter_upwards [eventually_ge_atTop R] with r hr z _ hz;
                                   rw [hR z (hr.trans hz),norm_zero])
  rwa [integral_sub ((hi 1).const_mul I) (hi I),integral_const_mul] at H

theorem dirPart_integrals_zero {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper)
    (hc : HasCompactSupport V) (hb : ∀ x : ℝ, V x=0) :
    (∫ z, dirPart 1 V z ∂upperArea)=0 ∧ (∫ z, dirPart I V z ∂upperArea)=0 := by
  have H := dir_curl_zero h hc hb
  have H' := dir_curl_zero (Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn h)
    (hc.comp_left (by simp : conj (0:ℂ)=0)) (by intro x; simp [hb])
  have he (v : ℂ) : (∫ z, dirPart v (fun w => conj (V w)) z ∂upperArea) =
      conj (∫ z, dirPart v V z ∂upperArea) := by
    rw [←integral_conj]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    exact dirPart_conj h (show 0≤z.im from (show 0<z.im from hz).le) _
  change I*(∫ z, dirPart 1 (fun w => conj (V w)) z ∂upperArea)-
    (∫ z, dirPart I (fun w => conj (V w)) z ∂upperArea)=0 at H'
  rw [he,he] at H'
  have W := congrArg conj H'
  simp only [map_sub,map_mul,Complex.conj_I,Complex.conj_conj,map_zero,neg_mul] at W
  have hY : (∫ z, dirPart I V z ∂upperArea)=0 := by linear_combination (-1/2:ℂ)*H+(-1/2:ℂ)*W
  rw [hY,sub_zero,mul_eq_zero] at H
  exact ⟨H.resolve_left Complex.I_ne_zero,hY⟩

theorem dirichlet_green_swap {V K : ℂ → ℂ} (hV : ContDiffOn ℝ ∞ V closedUpper)
    (hK : ContDiffOn ℝ ∞ K closedUpper) (hc : HasCompactSupport V)
    (hV₀ : ∀ x : ℝ, V x=0) (hK₀ : ∀ x : ℝ, K x=0) :
    (∫ z, K z*dirLap V z ∂upperArea)=(∫ z, V z*dirLap K z ∂upperArea) := by
  let A := fun v : ℂ => K*dirPart v V-V*dirPart v K
  have hd (v : ℂ) : ContDiffOn ℝ ∞ (A v) closedUpper :=
    (hK.mul (dirPart_smooth hV v)).sub (hV.mul (dirPart_smooth hK v))
  have hh (v : ℂ) : HasCompactSupport (A v) := (dirPart_compact hc v).mul_left.sub hc.mul_right
  have hb (v : ℂ) (x : ℝ) : A v x=0 := by simp [A,hK₀,hV₀]
  have h (v : ℂ) (z : ℂ) (hz : z∈upper) :
      dirPart v (A v) z = K z*dirPart v (dirPart v V) z-V z*dirPart v (dirPart v K) z := by
    have D {g : ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g closedUpper) :=
      ((hg z (show 0≤z.im from (show 0<z.im from hz).le)).contDiffAt (closedUpper_nhds hz)).differentiableAt (by simp)
    have dd := ((D hK).hasFDerivAt.mul (D (dirPart_smooth hV v)).hasFDerivAt).sub
      ((D hV).hasFDerivAt.mul (D (dirPart_smooth hK v)).hasFDerivAt)
    rw [dirPart_inside _ _ hz,(show HasFDerivAt (A v) _ z from dd).fderiv]
    simp only [dirPart_inside _ _ hz,sub_apply,add_apply,smul_apply,smul_eq_mul]
    ring
  have hi (v : ℂ) := closed_integrable_compact (dirPart_smooth (hd v) v).continuousOn (dirPart_compact (hh v) v)
  have h₁ := (dirPart_integrals_zero (hd 1) (hh 1) (hb 1)).1
  have h₂ := (dirPart_integrals_zero (hd I) (hh I) (hb I)).2
  have he : (∫ z, K z*dirLap V z-V z*dirLap K z ∂upperArea)=0 := by
    have H := congrArg₂ (·+·) h₁ h₂
    rw [zero_add,←integral_add (hi 1) (hi I)] at H
    apply Eq.trans _ H
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    simp only [h _ _ hz,dirLap,Pi.add_apply]; ring
  have hcomp : HasCompactSupport (dirLap V) := (dirPart_compact (dirPart_compact hc 1) 1).add (dirPart_compact (dirPart_compact hc I) I)
  have hiV := closed_integrable_compact (hK.mul (dirLap_smooth hV)).continuousOn hcomp.mul_left
  have hiK := closed_integrable_compact (hV.mul (dirLap_smooth hK)).continuousOn hc.mul_right
  erw [integral_sub hiV hiK] at he
  exact sub_eq_zero.mp he

end Liu
