import Liu.Comparability

noncomputable section
open Set Real
namespace Liu

theorem PickSum.power_two_sided {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0 ≤ t) :
    ∃ c > 0, ∀ z : ℂ, 0 ≤ z.im →
      c/(1+‖z‖)^t ≤ ‖p.power t z‖ ∧ ‖p.power t z‖ ≤ p.bound^t/(1+‖z‖)^t := by
  obtain ⟨c,hc,h⟩ := p.two_sided_decay
  refine ⟨c^t,rpow_pos_of_pos hc _,?_⟩
  intro z hz
  obtain ⟨hl,hu⟩ := h z hz
  change _ ≤ ‖(p.value z)^(t:ℂ)‖ ∧ _
  rw [Complex.norm_cpow_real]
  constructor
  · rw [← div_rpow hc.le (by positivity)]
    exact rpow_le_rpow (by positivity) hl ht
  · change ‖(p.value z)^(t:ℂ)‖ ≤ _
    rw [Complex.norm_cpow_real,←div_rpow p.bound_pos.le (by positivity)]
    exact rpow_le_rpow (norm_nonneg _) hu ht

/-- A representative continuous on the closed half-plane with the decay proved in B.1
satisfies the actual domination inequality of Lemma 3.2 for the finite-sum powers. -/
theorem PickSum.domination_of_decaying_representative {n : ℕ} (p : PickSum n) {t : ℝ}
    (ht : 0 ≤ t) (G : ℂ → ℂ)
    (hcont : ContinuousOn G {z : ℂ | 0 ≤ z.im})
    (hfar : ∃ R > 0, ∃ M > 0, ∀ z : ℂ, 0 ≤ z.im → R < ‖z‖ →
      ‖G z‖ ≤ M/(1+‖z‖)^t) :
    ∃ C > 0, ∀ z ∈ upper, ‖G z‖ ≤ C * ‖p.power t z‖ * (1+|log ‖p.power t z‖|) := by
  obtain ⟨c,hc,h⟩ := p.power_two_sided ht
  obtain ⟨R,hR,M,hM,hlarge⟩ := hfar
  let K := Metric.closedBall (0:ℂ) R ∩ {z : ℂ | 0 ≤ z.im}
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) R).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hne : K.Nonempty := ⟨0,by simp [K,hR.le]⟩
  have hweight : Continuous (fun z : ℂ => (1+‖z‖)^t) := by fun_prop (disch := positivity)
  have hC : ContinuousOn (fun z => ‖G z‖*(1+‖z‖)^t) K :=
    (hcont.norm.mono inter_subset_right).mul hweight.continuousOn
  obtain ⟨w,_,hw⟩ := hK.exists_isMaxOn hne hC
  let A := max M (‖G w‖*(1+‖w‖)^t)
  have hA : 0 < A := hM.trans_le (le_max_left ..)
  refine ⟨A/c,div_pos hA hc,?_⟩
  intro z hz
  have hd : 0 < (1+‖z‖)^t := rpow_pos_of_pos (by positivity) _
  have hb : ‖G z‖*(1+‖z‖)^t ≤ A := by
    by_cases hh : ‖z‖ ≤ R
    · exact (hw (show z ∈ K from ⟨by simpa using hh,show 0 ≤ z.im from le_of_lt hz⟩)).trans (le_max_right ..)
    · exact ((le_div_iff₀ hd).mp (hlarge z (le_of_lt hz) (lt_of_not_ge hh))).trans (le_max_left ..)
  have hl := (div_le_iff₀ hd).mp (h z (le_of_lt hz)).1
  have hratio : ‖G z‖ ≤ A/c*‖p.power t z‖ := by
    apply (mul_le_mul_iff_left₀ hd).mp
    calc
      _ ≤ A := hb
      _ = (A/c)*c := (div_mul_cancel₀ _ hc.ne').symm
      _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hl (div_pos hA hc).le
  exact hratio.trans (le_mul_of_one_le_right (by positivity) (by linarith [abs_nonneg (log ‖p.power t z‖)]))

end Liu
