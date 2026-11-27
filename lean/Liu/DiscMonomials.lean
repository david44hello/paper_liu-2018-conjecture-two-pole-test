module

public import Liu.CauchyDisc
public import Liu.CapWeights

@[expose] public section

noncomputable section
open Set MeasureTheory Real Metric Filter
open scoped ComplexConjugate Topology
namespace Liu

/-- Normalized disc monomials with their actual complex inner products. -/
private theorem phase_power_mean {k : ℕ} (hk : k≠0) :
    (∫ θ in Ioo (-π) π, (unitPhase θ)^k)=0 := by
  let f := fun w : ℂ => w^k
  have hd : DiffContOnCl ℂ f (ball 0 |(1:ℝ)|) := (show Differentiable ℂ f by dsimp [f]; fun_prop).diffContOnCl
  have h := hd.circleAverage
  unfold circleAverage at h
  have hper := ((periodic_circleMap (0:ℂ) 1).comp f).intervalIntegral_add_eq (-π) 0
  rw [show -π+2*π=π by ring,zero_add] at hper
  dsimp only [Function.comp_apply] at hper
  have hzero : (∫ θ in (0:ℝ)..2*π, f (circleMap 0 1 θ))=0 := by
    change (2*π)⁻¹ • (∫ θ in (0:ℝ)..2*π, f (circleMap 0 1 θ))=f 0 at h
    rw [show f 0=0 from zero_pow hk,smul_eq_zero] at h
    exact h.resolve_left (inv_ne_zero (by positivity))
  rw [←hper,intervalIntegral.integral_of_le (by linarith [pi_pos]),integral_Ioc_eq_integral_Ioo] at hzero
  simpa [f,circleMap,unitPhase] using hzero

private theorem phase_monomial_mean (n m : ℕ) :
    (∫ θ in Ioo (-π) π, unitPhase θ^n*conj (unitPhase θ^m)) =
      if n=m then ((2*π:ℝ):ℂ) else 0 := by
  have cancel (θ : ℝ) (j : ℕ) : unitPhase θ^j*conj (unitPhase θ^j)=1 := by
    rw [Complex.mul_conj',norm_pow,unitPhase_norm]; simp
  rcases lt_trichotomy n m with h | h | h
  · rw [if_neg h.ne]
    have he (θ : ℝ) : unitPhase θ^n*conj (unitPhase θ^m)=conj (unitPhase θ^(m-n)) := by
      conv_lhs => rw [show m=n+(m-n) by omega,pow_add,map_mul,←mul_assoc,cancel,one_mul]
    simp_rw [he,integral_conj,phase_power_mean (show m-n≠0 by omega),map_zero]
  · subst m; simp only [cancel,if_pos rfl,setIntegral_const,Real.volume_real_Ioo_of_le (by linarith [pi_pos] : -π≤π)]
    simp [Complex.real_smul]; push_cast; ring
  · rw [if_neg h.ne']
    have he (θ : ℝ) : unitPhase θ^n*conj (unitPhase θ^m)=unitPhase θ^(n-m) := by
      conv_lhs => rw [show n=(n-m)+m by omega,pow_add,mul_assoc,cancel,mul_one]
    simp_rw [he,phase_power_mean (show n-m≠0 by omega)]

theorem disc_monomial_pairing (n m : ℕ) :
    (∫ z in disc, z^n*conj (z^m) ∂area) = if n=m then ((n:ℂ)+1)⁻¹ else 0 := by
  classical
  let radial := fun r : ℝ => ((r:ℂ)^(n+m+1))
  let angular := fun θ => unitPhase θ^n*conj (unitPhase θ^m)
  let Ω := Ioo (0:ℝ) 1 ×ˢ Ioo (-π) π
  have hsep : (∫ z in disc, z^n*conj (z^m) ∂volume) =
      (∫ r in Ioo (0:ℝ) 1, radial r)*(∫ θ in Ioo (-π) π, angular θ) := by
    have hdiscM : MeasurableSet disc := Metric.isOpen_ball.measurableSet
    rw [←integral_indicator hdiscM,
      ←Complex.integral_comp_polarCoord_symm,polarCoord_target,←setIntegral_prod_mul,Measure.volume_eq_prod]
    have hs : Ω ⊆ Ioi (0:ℝ) ×ˢ Ioo (-π) π := fun p hp => ⟨hp.1.1,hp.2⟩
    rw [show (Ioo (0:ℝ) 1 ×ˢ Ioo (-π) π)=Ω from rfl,←inter_eq_right.mpr hs,←setIntegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo : MeasurableSet Ω)]
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    have hn := Complex.norm_polarCoord_symm p
    rw [abs_of_pos hp.1] at hn
    have hdisc : Complex.polarCoord.symm p∈disc ↔ p.1<1 := by change dist _ (0:ℂ)<1 ↔ _; rw [dist_zero_right,hn]
    change p.1 • disc.indicator _ (Complex.polarCoord.symm p)=Ω.indicator _ p
    by_cases h : p.1<1
    · rw [indicator_of_mem (hdisc.mpr h),indicator_of_mem (show p∈Ω from ⟨⟨hp.1,h⟩,hp.2⟩)]
      simp only [polarRay_coord,polarRay,radial,angular,Complex.real_smul,mul_pow,map_mul,map_pow,Complex.conj_ofReal,pow_add,pow_one]
      ring
    · rw [indicator_of_notMem (mt hdisc.mp h),indicator_of_notMem (show p∉Ω from fun hp => h hp.1.2),smul_zero]
  unfold area
  rw [Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤1/π),hsep]
  change (1/π:ℝ) • ((∫ r in Ioo (0:ℝ) 1, radial r)*(∫ θ in Ioo (-π) π, unitPhase θ^n*conj (unitPhase θ^m)))=_
  rw [phase_monomial_mean]; split
  · rename_i h; subst m
    have hi : (∫ r in Ioo (0:ℝ) 1, radial r)=(1/((n:ℝ)+n+2):ℝ) := by
      dsimp only [radial]; simp_rw [←Complex.ofReal_pow]
      rw [integral_complex_ofReal,←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le zero_le_one,integral_pow]
      push_cast; norm_num <;> ring_nf
    rw [hi,Complex.real_smul]; push_cast
    rw [show (n:ℂ)+n+2=2*((n:ℂ)+1) by ring]
    field_simp [Complex.ofReal_ne_zero.mpr pi_ne_zero]
  · simp

end Liu
