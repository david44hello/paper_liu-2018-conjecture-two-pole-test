module

public import Liu.Comparability
public import Liu.RadialEnergy

@[expose] public section

noncomputable section
open Set MeasureTheory Real
namespace Liu

private theorem uniform_rpow_bound {x K e b : ℝ} (hx : 0 ≤ x) (hxK : x ≤ K)
    (hK : 1 ≤ K) (he : 0 ≤ e) (heb : e ≤ b) : x^e ≤ K^b :=
  (rpow_le_rpow hx hxK he).trans (rpow_le_rpow_of_exponent_le hK heb)

private theorem uniform_rpow_lipschitz {a b K q : ℝ} (hK : 1 ≤ K)
    (ha : a ∈ Icc 0 K) (hb : b ∈ Icc 0 K) (hq : q ∈ Icc 2 4) :
    |a^q-b^q| ≤ (4*K^3)*|a-b| := by
  have qpos : 1 ≤ q := le_trans (by norm_num) hq.1
  let f : ℝ → ℝ := fun x => x^q
  have der (x : ℝ) : HasDerivAt f (q * x^(q-1)) x := Real.hasDerivAt_rpow_const (Or.inr qpos)
  have bound (x : ℝ) (hx : x ∈ Icc 0 K) : ‖deriv f x‖ ≤ 4*K^3 := by
    rw [(der x).deriv,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by linarith) (rpow_nonneg hx.1 _))]
    have hu := uniform_rpow_bound hx.1 hx.2 hK (sub_nonneg.mpr qpos) (show q-1 ≤ 3 by linarith [hq.2])
    rw [rpow_ofNat] at hu
    exact mul_le_mul hq.2 hu (rpow_nonneg hx.1 _) (by norm_num)
  simpa only [Real.norm_eq_abs,f] using
    (convex_Icc (0:ℝ) K).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => (der x).differentiableAt) bound hb ha

private theorem PickSum.farBound_nonneg {n : ℕ} (p : PickSum n) : 0 ≤ p.farBound := by
  have h := p.far_remainder (z:=0) (by simp)
  simpa using (norm_nonneg _).trans h

/-- On the exterior of the unit disc, subtracting the exact radial pole model leaves
an integrable bound of order r⁻³, uniform for exponents from two to four. -/
theorem PickSum.power_tail_error {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ q ∈ Icc (2:ℝ) 4, ∀ z : ℂ, 0 ≤ z.im → 1 < ‖z‖ →
      |‖p.value z‖^q - p.mass^q*‖z‖^(-q)| ≤ C*‖z‖^(-3:ℝ) := by
  let K := max 1 (max p.mass p.bound)
  have hK : 1 ≤ K := le_max_left ..
  have hm : p.mass ≤ K := (le_max_left ..).trans (le_max_right ..)
  have hb : p.bound ≤ K := (le_max_right ..).trans (le_max_right ..)
  have hJ := p.farBound_nonneg
  refine ⟨4*K^3*p.farBound,by positivity,?_⟩
  intro q hq z hz hr
  have hr0 : 0 < ‖z‖ := zero_lt_one.trans hr
  have hd : 0 < 1+‖z‖ := by positivity
  have hv := (le_div_iff₀ hd).mp (p.global_decay hz)
  have ha : ‖z‖*‖p.value z‖ ≤ K := by nlinarith [norm_nonneg (p.value z)]
  have hlip := uniform_rpow_lipschitz hK ⟨by positivity,ha⟩ ⟨p.mass_pos.le,hm⟩ hq
  have hsub := p.radial_error hz
  have hsmall : p.farBound/(1+‖z‖) ≤ p.farBound/‖z‖ :=
    div_le_div_of_nonneg_left hJ hr0 (by linarith)
  have bound := hlip.trans (mul_le_mul_of_nonneg_left (hsub.trans hsmall) (by positivity))
  have factor : ‖p.value z‖^q - p.mass^q*‖z‖^(-q) =
      ((‖z‖*‖p.value z‖)^q-p.mass^q)*‖z‖^(-q) := by
    rw [mul_rpow hr0.le (norm_nonneg _),rpow_neg hr0.le]
    field_simp [(rpow_pos_of_pos hr0 q).ne']
  rw [factor,abs_mul,abs_of_nonneg (rpow_nonneg hr0.le _)]
  calc
    _ ≤ ((4*K^3)*(p.farBound/‖z‖))*‖z‖^(-2:ℝ) :=
      mul_le_mul bound (rpow_le_rpow_of_exponent_le hr.le (by linarith [hq.1]))
        (rpow_nonneg hr0.le _) (by positivity)
    _ = _ := by
      simp only [Real.rpow_neg hr0.le,Real.rpow_ofNat]
      ring

theorem PickSum.uniform_energy_error {n : ℕ} (p : PickSum n) :
    ∃ B : ℝ, ∀ q : ℝ, 2 < q → q ≤ 4 →
      |(∫ z, ‖p.value z‖^q ∂upperArea) - p.mass^q/(q-2)| ≤ B := by
  classical
  obtain ⟨C,hC,hfar⟩ := p.power_tail_error
  let K := max 1 p.bound
  let D := Metric.closedBall (0:ℂ) 1
  let core := D.indicator (fun _ => K^4)
  have hcoreV : Integrable core volume := by
    apply (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr
    exact integrableOn_const (measure_closedBall_lt_top ..).ne
  have hcore : Integrable core upperArea := (hcoreV.smul_measure ENNReal.ofReal_ne_top).restrict
  have htInt (q : ℝ) (hq : 2 < q) : Integrable (radialTail q) upperArea := by
    apply Integrable.of_integral_ne_zero
    rw [radialTail_integral hq]
    positivity
  have hg := hcore.add ((htInt 3 (by norm_num)).const_mul C)
  refine ⟨∫ z, core z + C*radialTail 3 z ∂upperArea,?_⟩
  intro q hq hq4
  have hi := p.norm_power_integrable hq
  have hj := (htInt q hq).const_mul (p.mass^q)
  have eq : (∫ z, ‖p.value z‖^q-p.mass^q*radialTail q z ∂upperArea) =
      (∫ z, ‖p.value z‖^q ∂upperArea)-p.mass^q/(q-2) := by
    rw [integral_sub hi hj,integral_const_mul,radialTail_integral hq]
    ring
  rw [← eq,← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hg
  filter_upwards [ae_restrict_mem (μ := area) upper_open.measurableSet] with z hz
  change ‖‖p.value z‖^q-p.mass^q*radialTail q z‖ ≤ core z + C*radialTail 3 z
  rw [Real.norm_eq_abs]
  by_cases h : 1 < ‖z‖
  · have hD : z ∉ D := by simpa [D] using not_le.mpr h
    simpa [core,hD,radialTail,h] using hfar q ⟨hq.le,hq4⟩ z (le_of_lt hz) h
  · have hD : z ∈ D := by simpa [D] using le_of_not_gt h
    have hnorm := (p.global_decay (le_of_lt hz)).trans (div_le_self p.bound_pos.le (by linarith [norm_nonneg z]))
    have hu := uniform_rpow_bound (norm_nonneg _) (hnorm.trans (le_max_right 1 p.bound))
      (le_max_left 1 p.bound) (by linarith : 0 ≤ q) hq4
    simpa [core,hD,radialTail,h,abs_of_nonneg (rpow_nonneg (norm_nonneg _) q),K] using hu

end Liu
