import Liu.EnergyEstimate

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology ENNReal
namespace Liu

theorem energy_eq_integral {F : ℂ → ℂ} (h : MemLp F 2 upperArea) :
    energy F = ∫ z, ‖F z‖^2 ∂upperArea := by
  have hn : 0 ≤ ∫ z, ‖F z‖^2 ∂upperArea := integral_nonneg fun _ => sq_nonneg _
  simp only [energy,asL2,dif_pos h,Lp.norm_toLp,h.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hn _), ← Real.sqrt_eq_rpow,Real.sq_sqrt hn]

theorem PickSum.power_energy {n : ℕ} (p : PickSum n) {ε : ℝ} (he : 0 < ε) :
    energy (p.power (1+ε)) = ∫ z, ‖p.value z‖^(2+2*ε) ∂upperArea := by
  rw [energy_eq_integral (p.power_memLp_two (by linarith : 1 < 1+ε))]
  apply integral_congr_ae
  filter_upwards with z
  change ‖(p.value z)^((1+ε:ℝ):ℂ)‖^2 = _
  rw [Complex.norm_cpow_real,← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

/-- The exact leading coefficient in Proposition 3.3 for each nonempty finite Pick sum.
The proof controls the error uniformly up to ε=1, with normalized half-plane area. -/
theorem PickSum.denominator_limit {n : ℕ} (p : PickSum n) :
    Tendsto (fun ε : ℝ => ε*energy (p.power (1+ε))) (𝓝[>] 0) (𝓝 (p.mass^2/2)) := by
  obtain ⟨B,hB⟩ := p.uniform_energy_error
  have he0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
  have he1 := he0.eventually_lt_const (show (0:ℝ)<1 by norm_num)
  have hzero : Tendsto (fun ε : ℝ => ε*energy (p.power (1+ε))-p.mass^(2+2*ε)/2)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun ε : ℝ => ε*B) _ (by simpa using he0.mul_const B)
    filter_upwards [hp,he1] with ε he he'
    have hq : 2 < 2+2*ε := by linarith
    have h := hB (2+2*ε) hq (by linarith)
    rw [← p.power_energy he] at h
    have heq : ε*energy (p.power (1+ε))-p.mass^(2+2*ε)/2 =
        ε*(energy (p.power (1+ε)) - p.mass^(2+2*ε)/(2+2*ε-2)) := by
      field_simp [show 2+2*ε-2 ≠ 0 by linarith,he.ne']
      <;> ring
    rw [Real.norm_eq_abs,heq,abs_mul,abs_of_pos he]
    exact mul_le_mul_of_nonneg_left h he.le
  have hmodel : Tendsto (fun ε : ℝ => p.mass^(2+2*ε)/2) (𝓝[>] 0) (𝓝 (p.mass^2/2)) := by
    have hcont : Continuous (fun ε : ℝ => p.mass^(2+2*ε)/2) := by
      have hm := p.mass_pos.ne'
      fun_prop (disch := assumption)
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa only [sub_add_cancel,zero_add] using hzero.add hmodel

theorem Pair.denominator_limit (p : Pair) :
    Tendsto (fun ε : ℝ => ε*energy (critical p ε)) (𝓝[>] 0) (𝓝 (p.mass^2/2)) := by
  have hm : p.toPick.mass = p.mass := by simp [PickSum.mass,Pair.mass,Pair.toPick,Fin.sum_univ_two]
  simpa only [Pair.toPick_power,hm] using p.toPick.denominator_limit

theorem two_pole_test_of_residual (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) (hcoinc : coincidentDeficit)
    (hsmall : smallMassDeficit) (hI : FinitePartInvariances)
    (hfinite : finitePartExists p.value)
    (hnum : Tendsto (fun ε => residual (critical p ε)) (𝓝[>] 0) (𝓝 (k₀*p.mass^2-deficit p.value))) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2 < deficit p.value ∧ p.slope < 0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → p.quotientDomain ε ∧ quotient (critical p ε) < k₀ :=
  conditional_two_pole_test p hbox hflux h54 hE4 hcoinc hsmall hI hfinite p.denominator_limit hnum

end Liu
