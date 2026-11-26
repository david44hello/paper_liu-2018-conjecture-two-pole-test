import Liu.RadialField
import Liu.AngularPotential

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

private def modelAmplitude (m : ℝ) : ℂ := Complex.I*(m:ℂ)/2

private theorem model_direction_integrand (m : ℝ) (z h w : ℂ) :
    ((((h*greenResolvent z w).re):ℝ):ℂ)*radialSource m w =
      modelAmplitude m*(((h*radialKernel z w).re:ℝ):ℂ) := by
  let a := (‖w‖^2)⁻¹
  have hk : h*radialKernel z w=(h*greenResolvent z w)*(a:ℂ) := by
    dsimp [radialKernel,a]; push_cast; ring
  have hs : radialSource m w=modelAmplitude m*(a:ℂ) := by
    dsimp [radialSource,modelAmplitude,a]; push_cast; ring
  rw [hk,hs]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.ofReal_mul,Complex.ofReal_sub]; ring

private theorem model_direction_integral {z : ℂ} (hz : 0≤z.im) (hn : z≠0) (hi : Integrable (radialKernel z) upperArea)
    (m : ℝ) (h : ℂ) :
    Integrable (fun w => ((((h*greenResolvent z w).re):ℝ):ℂ)*radialSource m w) upperArea ∧
    (∫ w, ((((h*greenResolvent z w).re):ℝ):ℂ)*radialSource m w ∂upperArea) = angularDifferential m z h := by
  simp_rw [model_direction_integrand]
  have hj : Integrable (fun w => (h*radialKernel z w).re) upperArea := (hi.const_mul h).re
  refine ⟨hj.ofReal.const_mul _,?_⟩
  rw [integral_const_mul,integral_complex_ofReal]
  have he := integral_re (hi.const_mul h)
  change (∫ w, (h*radialKernel z w).re ∂upperArea) = (∫ w, h*radialKernel z w ∂upperArea).re at he
  rw [he,integral_const_mul,radialKernel_integral hz hn hi,angularDifferential_apply,upperAngle_eq hz hn]
  have alg : h*((2*Complex.I)*((z.arg-π/2:ℝ):ℂ)/z) = (h/z)*((2*Complex.I)*((z.arg-π/2:ℝ):ℂ)) := by ring
  rw [alg]
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero,zero_add,mul_one,sub_zero]
  dsimp only [modelAmplitude]; push_cast; ring

theorem PickSum.gradient_far_estimate {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → 1<‖z‖ →
      ‖fderiv ℝ (fun w => potential p.value w-angularPotential p.mass w) z‖ ≤ C*(1+log ‖z‖)/‖z‖^2 := by
  obtain ⟨C,hC,h⟩ := p.radial_field_comparison
  refine ⟨C,hC,?_⟩
  intro z hz hr
  have hn := norm_pos_iff.mp (zero_lt_one.trans hr)
  obtain ⟨hker,hI,hbound⟩ := h z hz hr
  have hK : 0≤p.derivativeBound/2 := by simpa using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  have hd := (p.potential_hasFDerivAt_closed hz).sub (angularPotential_hasFDerivAt p.mass hz hn)
  change ‖fderiv ℝ (potential p.value-angularPotential p.mass) z‖ ≤ _
  rw [hd.fderiv]
  have hl := log_nonneg hr.le
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  obtain ⟨hm,he⟩ := model_direction_integral hz hn hker p.mass a
  simp only [ContinuousLinearMap.sub_apply,greenDifferential_apply p.source_measurable hK
    (fun w hw => p.source_decay (le_of_lt hw)) hz]
  rw [←he,←integral_sub (greenDifferential_integrable_apply p.source_measurable hK
    (fun w hw => p.source_decay (le_of_lt hw)) hz a) hm]
  let g := fun w => ‖a‖*‖greenResolvent z w*(source p.value w-radialSource p.mass w)‖
  have hg : Integrable g upperArea := hI.norm.const_mul _
  have hnorm := norm_integral_le_of_norm_le hg (ae_of_all upperArea (fun w => show
    ‖((((a*greenResolvent z w).re):ℝ):ℂ)*source p.value w-
       ((((a*greenResolvent z w).re):ℝ):ℂ)*radialSource p.mass w‖ ≤ g w by
      rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (norm_nonneg _)).trans
      dsimp only [g]; simp only [norm_mul,mul_assoc,le_refl]))
  apply hnorm.trans
  simp only [g,integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hbound (norm_nonneg a)).trans_eq (mul_comm ..)

end Liu
