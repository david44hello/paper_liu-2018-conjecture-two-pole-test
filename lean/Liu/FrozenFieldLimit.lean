import Liu.PhysicalFreezing

noncomputable section
open Set MeasureTheory Real Filter Metric
open scoped ComplexConjugate Topology
namespace Liu

theorem PickSum.frozenSource_factor {n : ℕ} (p : PickSum n) (t : ℝ) {w : ℂ} (hw : 0≤w.im) :
    p.frozenLogSource t w=conj (p.parameterFactor t w)*(-Complex.I*source p.value w) := by
  rw [(p.critical_source_identity t hw).2]
  have hn : p.value w≠0 := fun he => by have hi := p.value_im_pos hw; simp [he] at hi
  rw [dbar_logInput (p.hasDerivAt hw).differentiableAt.hasDerivAt hn]
  simp only [PickSum.parameterFactor,map_mul,Complex.conj_ofReal,source]
  ring_nf <;> simp [Complex.I_sq] <;> ring

theorem PickSum.frozen_source_quadratic_bound {n : ℕ} (p : PickSum n) :
    ∃ K ≥ 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ w ∈ upper, ‖p.frozenLogSource t w‖ ≤ K/(1+‖w‖)^2 := by
  let M := max 1 p.bound
  have hm : 1≤M := le_max_left ..
  have hM := zero_lt_one.trans_le hm
  let B := p.derivativeBound/2
  have hB : 0≤B := by simpa [B] using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  refine ⟨2*M*B,by positivity,?_⟩
  intro t ht w hw
  have hz : 0≤w.im := le_of_lt hw
  have hv := (p.global_decay hz).trans ((div_le_self p.bound_pos.le (by linarith [norm_nonneg w])).trans (le_max_right 1 p.bound))
  have hp : ‖p.power t w‖≤M := by
    change ‖p.value w^(t:ℂ)‖≤M
    rw [Complex.norm_cpow_real]
    exact (rpow_le_rpow (norm_nonneg _) hv ht.1).trans ((rpow_le_rpow_of_exponent_le hm ht.2).trans_eq (rpow_one _))
  rw [p.frozenSource_factor t hz]
  simp only [PickSum.parameterFactor,norm_mul,Complex.norm_conj,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg (by linarith [ht.1] : 0≤1+t)]
  apply (mul_le_mul (mul_le_mul (by linarith [ht.2] : 1+t≤2) hp (norm_nonneg _) (by norm_num)) (p.source_decay hz) (norm_nonneg _) (by positivity)).trans_eq
  ring

private theorem frozen_measurable {n : ℕ} (p : PickSum n) (t : ℝ) : Measurable (p.frozenLogSource t) := by
  have hv := p.power_measurable 1
  change Measurable (fun w => p.value w^((1:ℝ):ℂ)) at hv
  have hV : Measurable p.value := by simpa using hv
  have hD := measurable_deriv (p.power (1+t))
  unfold PickSum.frozenLogSource; fun_prop

private theorem resolvent_dominates {f : ℂ → ℂ} {K : ℝ} (hK : 0≤K)
    (hb : ∀ w ∈ upper, ‖f w‖≤K/(1+‖w‖)^2) {z : ℂ} (hz : 0≤z.im) :
    ∀ᵐ w ∂upperArea, ‖greenResolvent z w*f w‖ ≤ (2*K)*gradientWeight z w := by
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,upperArea_ae_ne z] with w hw hn
  rw [norm_mul]
  apply (mul_le_mul (greenResolvent_bound hz hw hn.symm) (hb w hw) (norm_nonneg _) (by positivity)).trans
  calc
    _ = (2*K)*(‖z-w‖⁻¹/(1+‖w‖)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (gradientWeight_majorizes z w) (by positivity)

theorem PickSum.frozenField_uniform_bound {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ z : ℂ, 0≤z.im → ‖canonicalField (p.frozenLogSource t) z‖≤C := by
  obtain ⟨K,hK,h⟩ := p.frozen_source_quadratic_bound
  obtain ⟨A,hA,hw⟩ := gradientWeight_integral
  refine ⟨2*K*A,by positivity,?_⟩
  intro t ht z hz
  have hq : QuadraticDecay (p.frozenLogSource t) := ⟨frozen_measurable p t,K,hK,h t ht⟩
  rw [canonicalField_eq_integral hq,norm_neg]
  apply (norm_integral_le_of_norm_le ((hw z).1.const_mul (2*K)) (resolvent_dominates hK (h t ht) hz)).trans
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hw z).2 (by positivity)

theorem PickSum.frozenField_limit {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0≤z.im) :
    Tendsto (fun t : ℝ => canonicalField (p.frozenLogSource t) z) (𝓝[>] 0) (𝓝 (-Complex.I*field p.value z)) := by
  obtain ⟨K,hK,hb⟩ := p.frozen_source_quadratic_bound
  obtain ⟨_,_,hw⟩ := gradientWeight_integral
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have he : ∀ᶠ t in 𝓝[>] (0:ℝ), t∈Icc (0:ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),ht0.eventually_lt_const zero_lt_one] with t hp ht using ⟨hp.le,ht.le⟩
  let k := greenResolvent z
  have hk : Measurable k := by change Measurable (greenResolvent z); unfold greenResolvent; fun_prop
  have hlim : Tendsto (fun t => ∫ w, k w*p.frozenLogSource t w ∂upperArea) (𝓝[>] (0:ℝ))
      (𝓝 (∫ w, k w*(-Complex.I*source p.value w) ∂upperArea)) := by
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ ((hw z).1.const_mul (2*K)) ?_
    · exact Eventually.of_forall fun t => (hk.mul (frozen_measurable p t)).aestronglyMeasurable
    · filter_upwards [he] with t ht using resolvent_dominates hK (hb t ht) hz
    · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
      have hp := ((p.parameterFactor_hasDerivAt 0 (le_of_lt hw)).continuousAt.tendsto.comp ht0)
      have hh := (Complex.continuous_conj.continuousAt.tendsto.comp hp).mul_const (-Complex.I*source p.value w)
      have hh' := hh.const_mul (k w)
      simp only [PickSum.parameterFactor,zero_add,add_zero,Complex.ofReal_zero,Complex.cpow_zero,
        PickSum.power,mul_one,Complex.ofReal_one,map_one,one_mul, Function.comp_apply] at hh'
      apply hh'.congr'
      filter_upwards with t
      rw [p.frozenSource_factor t (le_of_lt hw)]
      rfl
  have hneg := hlim.neg
  have heq : (∫ w, k w*(-Complex.I*source p.value w) ∂upperArea) = -Complex.I*∫ w, k w*source p.value w ∂upperArea := by
    rw [←integral_const_mul]
    apply integral_congr_ae; filter_upwards with w; ring
  rw [heq] at hneg
  rw [p.field_eq_canonical hz,canonicalField_eq_integral p.source_quadratic]
  rw [show -(-Complex.I*∫ w, k w*source p.value w ∂upperArea) =
      -Complex.I*(-∫ w, k w*source p.value w ∂upperArea) by ring] at hneg
  apply hneg.congr'
  filter_upwards [he] with t ht
  exact (canonicalField_eq_integral (show QuadraticDecay _ from ⟨frozen_measurable p t,K,hK,hb t ht⟩) z).symm

end Liu
