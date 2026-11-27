module

public import Liu.FarPole
public import Liu.Source

@[expose] public section

noncomputable section
open Set
namespace Liu

theorem PickSum.mass_pos {n : ℕ} (p : PickSum n) : 0 < p.mass := by
  haveI : Nonempty (Fin n) := ⟨⟨0,p.nonempty⟩⟩
  exact Finset.sum_pos (fun i _ => p.pos i) Finset.univ_nonempty

theorem PickSum.radial_error {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0 ≤ z.im) :
    |‖z‖ * ‖p.value z‖ - p.mass| ≤ p.farBound/(1+‖z‖) := by
  have h := abs_norm_sub_norm_le (z * p.value z) (-(p.mass:ℂ))
  rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos p.mass_pos,sub_neg_eq_add] at h
  exact h.trans (p.far_remainder hz)

/-- The global two-sided comparison includes points on the real axis. -/
theorem PickSum.two_sided_decay {n : ℕ} (p : PickSum n) :
    ∃ c > 0, ∀ z : ℂ, 0 ≤ z.im →
      c/(1+‖z‖) ≤ ‖p.value z‖ ∧ ‖p.value z‖ ≤ p.bound/(1+‖z‖) := by
  let R := max 1 (2*p.farBound/p.mass)
  let K := Metric.closedBall (0:ℂ) R ∩ {z : ℂ | 0 ≤ z.im}
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) R).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hne : K.Nonempty := ⟨0,by simp [K,hR.le]⟩
  have hc : ContinuousOn (fun z => ‖p.value z‖) K := fun z hz =>
    (p.hasDerivAt hz.2).continuousAt.norm.continuousWithinAt
  obtain ⟨w,hw,hmin⟩ := hK.exists_isMinOn hne hc
  have hn : 0 < ‖p.value w‖ := norm_pos_iff.mpr (fun he => by
    have h := p.value_im_pos hw.2; simp [he] at h)
  let c := min ‖p.value w‖ (p.mass/2)
  have hp := p.mass_pos
  have hcp : 0 < c := lt_min hn (by positivity)
  refine ⟨c,hcp,fun z hz => ⟨?_,p.global_decay hz⟩⟩
  have hd : 0 < 1+‖z‖ := by positivity
  by_cases core : ‖z‖ ≤ R
  · have hzk : z ∈ K := ⟨by simpa using core,hz⟩
    exact (div_le_self hcp.le (by linarith [norm_nonneg z])).trans
      ((min_le_left ..).trans (hmin hzk))
  · have hRz := (le_max_right 1 (2*p.farBound/p.mass)).trans (le_of_not_ge core)
    have hB := (div_le_iff₀ hp).mp hRz
    have he := (abs_le.mp (p.radial_error hz)).1
    have hsmall : p.farBound/(1+‖z‖) ≤ p.mass/2 :=
      (div_le_iff₀ hd).mpr (by nlinarith)
    apply (div_le_iff₀ hd).mpr
    have hc₂ : c ≤ p.mass/2 := min_le_right .. 
    nlinarith [norm_nonneg (p.value z)]

end Liu
