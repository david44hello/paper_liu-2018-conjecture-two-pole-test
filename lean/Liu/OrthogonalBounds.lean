import Liu.FarFieldClaim

noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate Topology
namespace Liu

theorem PickSum.potential_bounded {n : ℕ} (p : PickSum n) :
    ∃ B ≥ 0, ∀ z : ℂ, 0≤z.im → ‖potential p.value z‖ ≤ B := by
  obtain ⟨K,hK,h⟩ := p.potential_far_estimate
  let U := {z : ℂ | 0≤z.im}
  have hU : IsClosed U := isClosed_le continuous_const Complex.continuous_im
  have hc : ContinuousOn (potential p.value) U :=
    fun z hz => (p.potential_hasFDerivAt_closed hz).continuousAt.continuousWithinAt
  have hball := (isCompact_closedBall (0:ℂ) 1).inter_right hU
  obtain ⟨B,hB⟩ := hball.exists_bound_of_continuousOn (hc.mono inter_subset_right)
  have hm := p.mass_pos
  refine ⟨|B|+K+p.mass/2*π^2,by positivity,?_⟩
  intro z hz
  by_cases hr : 1<‖z‖
  · have hp := zero_lt_one.trans hr
    have hΔ : ‖potential p.value z-angularPotential p.mass z‖ ≤ K := (h z hz hr).trans (by
      apply (div_le_iff₀ hp).mpr
      exact mul_le_mul_of_nonneg_left (by linarith [log_le_sub_one_of_pos hp]) hK)
    have hθ := Complex.arg_nonneg_iff.mpr hz
    have hπ := Complex.arg_le_pi z
    have hbase : ‖angularPotential p.mass z‖ ≤ p.mass/2*π^2 := by
      rw [angularPotential_eq _ hz (norm_pos_iff.mp hp),norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) hθ) (sub_nonneg.mpr hπ))]
      nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul hπ (by linarith : π-z.arg ≤ π) (sub_nonneg.mpr hπ) pi_pos.le)
        (show 0≤p.mass/2 by positivity)]
    have hh := norm_add_le (potential p.value z-angularPotential p.mass z) (angularPotential p.mass z)
    rw [sub_add_cancel] at hh
    linarith [abs_nonneg B]
  · have hh := hB z ⟨by simpa using le_of_not_gt hr,hz⟩
    linarith [le_abs_self B,mul_nonneg (show 0≤p.mass/2 by positivity) (sq_nonneg π)]

theorem PickSum.field_decay {n : ℕ} (p : PickSum n) :
    ∃ B ≥ 0, ∀ z ∈ upper, ‖field p.value z‖ ≤ B/(1+‖z‖) := by
  obtain ⟨A,hA,ha⟩ := p.field_bounded_upper
  obtain ⟨K,hK,hk⟩ := p.field_far_estimate
  let B := 2*(A+K+p.mass*π)
  have hm := p.mass_pos
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro z hz
  let r := ‖z‖
  have hR : 0<1+r := by dsimp [r]; positivity
  by_cases hr : 1<r
  · have hp := zero_lt_one.trans hr
    have hθ := Complex.arg_nonneg_iff.mpr (show 0≤z.im from le_of_lt hz)
    have hπ := Complex.arg_le_pi z
    have hfield := hk z (le_of_lt hz) hr
    have hbase : ‖fieldFarModel p.mass z‖ ≤ p.mass*π/r := by
      rw [fieldFarModel,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_neg,abs_of_pos hm]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [pi_pos],by linarith [pi_pos]⟩) hm.le) hp.le
    have hΔ : ‖field p.value z-fieldFarModel p.mass z‖ ≤ K/r := hfield.trans (by
      apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
      nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show 1+log r ≤ r by linarith [log_le_sub_one_of_pos hp]) hK) hp.le])
    have hh := norm_add_le (field p.value z-fieldFarModel p.mass z) (fieldFarModel p.mass z)
    rw [sub_add_cancel] at hh
    apply (hh.trans (add_le_add hΔ hbase)).trans
    rw [←add_div]
    apply (div_le_div_iff₀ hp hR).mpr
    dsimp only [B]
    nlinarith only [mul_le_mul_of_nonneg_left (show 1+r≤2*r by linarith) (by positivity : 0≤K+p.mass*π),mul_nonneg hA hp.le]
  · apply (ha z hz).trans
    apply (le_div_iff₀ hR).mpr
    dsimp only [B]
    nlinarith only [mul_le_mul_of_nonneg_left (show 1+r≤2 by linarith [le_of_not_gt hr]) hA,hK,mul_nonneg hm.le pi_pos.le]

theorem log_square_tail_bound {g : ℂ → ℂ} (hc : ContinuousOn g {z : ℂ | 0≤z.im}) {K T : ℝ} (hK : 0≤K)
    (h : ∀ z : ℂ, 0≤z.im → T≤‖z‖ → ‖g z‖ ≤ K*(1+log ‖z‖)/‖z‖^2) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → ‖g z‖ ≤ C/(1+‖z‖)^(3/2:ℝ) := by
  let R := max 1 T
  have hR : 1≤R := le_max_left ..
  let U := {z : ℂ | 0≤z.im}
  have hU : IsClosed U := isClosed_le continuous_const Complex.continuous_im
  have hcore := (isCompact_closedBall (0:ℂ) R).inter_right hU
  obtain ⟨B,hB⟩ := hcore.exists_bound_of_continuousOn (hc.mono inter_subset_right)
  let C := |B| *(1+R)^(3/2:ℝ)+3*K*(2:ℝ)^(3/2:ℝ)
  have hRp : 0<1+R := by linarith
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro z hz
  let r := ‖z‖
  have hp : 0<1+r := by dsimp [r]; positivity
  apply (le_div_iff₀ (rpow_pos_of_pos hp _)).mpr
  by_cases hh : r≤R
  · have hb := hB z ⟨by simpa using hh,hz⟩
    have hscale := rpow_le_rpow hp.le (by linarith : 1+r≤1+R) (by norm_num : (0:ℝ)≤3/2)
    apply (mul_le_mul (hb.trans (le_abs_self B)) hscale (by positivity) (abs_nonneg _)).trans
    dsimp only [C]; exact le_add_of_nonneg_right (by positivity)
  · have hr := lt_of_not_ge hh
    have hrp := zero_lt_one.trans_le (hR.trans hr.le)
    have hg := h z hz ((le_max_right ..).trans hr.le)
    have hlog : 1+log r ≤ 3*r^(1/2:ℝ) := by
      have hl := log_le_rpow_div hrp.le (by norm_num : (0:ℝ)<1/2)
      have hu := one_le_rpow (hR.trans hr.le) (by norm_num : 0≤(1/2:ℝ))
      linarith
    have hsc := rpow_le_rpow hp.le (by linarith : 1+r≤2*r) (by norm_num : (0:ℝ)≤3/2)
    rw [mul_rpow (by norm_num) hrp.le] at hsc
    have hu := mul_le_mul (hg.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hK) (sq_nonneg r)))
      hsc (by positivity) (by positivity)
    apply hu.trans
    have he : K*(3*r^(1/2:ℝ))/r^2*((2:ℝ)^(3/2:ℝ)*r^(3/2:ℝ))=3*K*(2:ℝ)^(3/2:ℝ) := by
      have hx : r^(1/2:ℝ)*r^(3/2:ℝ) = r^2 := by rw [←rpow_add hrp]; norm_num
      calc
        _ = (3*K*(2:ℝ)^(3/2:ℝ)/r^2)*(r^(1/2:ℝ)*r^(3/2:ℝ)) := by ring
        _ = _ := by rw [hx,div_mul_cancel₀ _ (pow_ne_zero _ hrp.ne')]
    rw [he]
    dsimp only [C]; exact le_add_of_nonneg_left (by positivity)

end Liu
