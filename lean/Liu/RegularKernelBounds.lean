import Liu.RegularResolvent
import Liu.GreenInterior

noncomputable section
open Set Metric Filter Real Complex MeasureTheory InnerProductSpace
open scoped Topology ComplexConjugate
namespace Liu

theorem regularResolvent_bounds :
    ∃ M≥0, ∀ (R : ℝ), 0<R → ∀ z : ℂ,
      (∀ w, ‖regularResolvent R z w‖≤M/R) ∧
      (∀ w, ‖Laplacian.laplacian (regularResolvent R z) w‖≤M/R^3) ∧
      (∀ w : ℂ, 0≤z.im → w∈upper → R≤‖z-w‖ →
        regularResolvent R z w=greenResolvent z w ∧ Laplacian.laplacian (regularResolvent R z) w=0) := by
  obtain ⟨B,hB,H⟩ := smoothInverse_bounds
  refine ⟨2*B,by positivity,fun R hR z => ⟨?_,?_,?_⟩⟩
  · intro w
    have bound (u : ℂ) : ‖scaledSmoothInverse R u‖≤R⁻¹*B := by
      rw [scaledSmoothInverse,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
      exact mul_le_mul_of_nonneg_left (H _).1 (inv_nonneg.mpr hR.le)
    exact (norm_sub_le ..).trans ((add_le_add (bound _) (bound _)).trans_eq (by ring))
  · intro w
    rw [regularResolvent_lap,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤R⁻¹^3)]
    apply (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (H _).2.1 (H _).2.1)) (by positivity : 0≤R⁻¹^3)).trans_eq
    ring
  · intro w hz hw hdist
    have hnorm (v : ℂ) (hv : R≤‖v‖) : 1/2<‖R⁻¹ • v‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),inv_mul_eq_div]
      apply (lt_div_iff₀ hR).mpr; linarith
    have hd := hnorm _ hdist
    have hr := hnorm _ (hdist.trans (distance_to_reflection_bound w z (le_of_lt hw) hz))
    have outer (v : ℂ) (hv : 1/2<‖R⁻¹ • v‖) : scaledSmoothInverse R v=v⁻¹ := by
      rw [scaledSmoothInverse,smoothInverse_outer hv.le,Complex.real_smul,Complex.real_smul,mul_inv_rev]
      push_cast; field_simp [Complex.ofReal_ne_zero.mpr hR.ne'] <;> ring
    rw [regularResolvent_lap,(H _).2.2 hr,(H _).2.2 hd,sub_self,smul_zero]
    exact ⟨by rw [regularResolvent,outer _ hr,outer _ hd,greenResolvent],rfl⟩

/-- The singular remainder is supported near the observation; its L¹ norm is O(R). -/
theorem local_resolvent_remainder {M R : ℝ} (hM : 0≤M) (hR : 0<R) (z : ℂ) (hz : z∈closedUpper)
    (hreg : ∀ w, ‖regularResolvent R z w‖≤M/R)
    (hout : ∀ w∈upper, R≤‖z-w‖ → regularResolvent R z w=greenResolvent z w) :
    ∀ᵐ w ∂upperArea, ‖greenResolvent z w-regularResolvent R z w‖≤
      ((2+M)/(2*R))*scaledWeight (2*R) z w := by
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,upperArea_ae_ne z] with w hw hn
  have hn' := norm_pos_iff.mpr (sub_ne_zero.mpr hn.symm)
  by_cases near : ‖z-w‖<R
  · have h := scaled_inverse_near (show 0<2*R by positivity) (show ‖z-w‖<2*R/2 by linarith)
    change scaledWeight (2*R) z w=_ at h
    rw [h,show (2+M)/(2*R)*(2*R*‖z-w‖⁻¹)=(2+M)*‖z-w‖⁻¹ by field_simp]
    exact (norm_sub_le ..).trans (by
      have H := add_le_add (greenResolvent_bound hz hw hn.symm) ((hreg w).trans (div_le_div_of_nonneg_left hM hn' near.le))
      rwa [div_eq_mul_inv,←add_mul] at H)
  · rw [hout w hw (le_of_not_gt near),sub_self,norm_zero]
    exact mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) _)

theorem upper_ball_indicator_bound (z : ℂ) {R : ℝ} (hR : 0<R) :
    Integrable (ball z R |>.indicator (fun _ : ℂ => (1:ℝ))) upperArea ∧
    (∫ w, (ball z R).indicator (fun _ : ℂ => (1:ℝ)) w ∂upperArea)≤R^2 := by
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  have hi : Integrable ((ball z R).indicator (fun _ : ℂ => (1:ℝ))) area :=
    (integrable_indicator_iff isOpen_ball.measurableSet).mpr (integrableOn_const (measure_ball_lt_top ..).ne)
  refine ⟨hi.restrict,(integral_mono_measure Measure.restrict_le_self (ae_of_all area (fun w => indicator_nonneg (fun _ _ => zero_le_one) w)) hi).trans_eq ?_⟩
  rw [integral_indicator isOpen_ball.measurableSet,setIntegral_const,smul_eq_mul,mul_one]
  simp [Measure.real,area,Complex.volume_ball,ENNReal.toReal_ofReal hR.le,NNReal.coe_real_pi]
  rw [ENNReal.toReal_ofReal (by positivity : 0≤π⁻¹)]
  field_simp

end Liu
