import Liu.Integrability

noncomputable section
open Set MeasureTheory
namespace Liu

theorem upper_open : IsOpen upper := isOpen_lt continuous_const Complex.continuous_im
theorem upperArea_ne_zero : upperArea ≠ 0 := by
  have hvol := upper_open.measure_pos (volume:Measure ℂ) (show upper.Nonempty from ⟨Complex.I,by simp [upper]⟩)
  intro he
  have hh := congrArg (fun μ : Measure ℂ => μ univ) he
  simp [upperArea,area] at hh
  rcases hh with h | h
  · linarith [Real.pi_pos]
  · exact hvol.ne' h

theorem PickSum.log_power_memLp_two {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 1<t) :
    MemLp (logInput (p.power t)) 2 upperArea := by
  have hf := p.power_measurable t
  have hmeas : Measurable (logInput (p.power t)) := by unfold logInput; fun_prop
  apply (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr
  have hh := p.weighted_power_integrable (v := 2) (by linarith : 0 < t) (by linarith : 2<t*2)
  apply hh.mono' (hmeas.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with z
  let x := ‖p.power t z‖
  let y := |Real.log x|
  have hy : 0 ≤ y := abs_nonneg _
  have h₂ : y^2 ≤ (1+y)^2 := by gcongr; linarith
  have h₅ : (1+y)^2 ≤ (1+y)^5 := pow_le_pow_right₀ (by linarith) (by decide)
  simp only [Real.norm_eq_abs,logInput,norm_mul,Complex.norm_real,
    Real.rpow_ofNat]
  rw [abs_of_nonneg (sq_nonneg _)]
  change (x*y)^2 ≤ x^2*(1+y)^5
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (h₂.trans h₅) (sq_nonneg _)

theorem PickSum.powerL2_norm_pos {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 1<t) :
    0 < ‖asL2 (p.power t)‖ := by
  have hf := p.power_memLp_two ht
  simp only [asL2,dif_pos hf,norm_pos_iff]
  intro hzero
  have hu : ∀ᵐ z ∂upperArea, z ∈ upper := ae_restrict_mem upper_open.measurableSet
  have hz : p.power t =ᵐ[upperArea] 0 :=
    hf.coeFn_toLp.symm.trans (hzero ▸ Lp.coeFn_zero ℂ 2 upperArea)
  haveI : NeZero upperArea := ⟨upperArea_ne_zero⟩
  obtain ⟨z,hz₁,hz₂⟩ := (hu.and hz).exists
  have hi := p.value_im_pos (le_of_lt hz₁)
  have hval : p.value z ≠ 0 := fun h => by simp [h] at hi
  exact (by simpa [PickSum.power,Complex.cpow_eq_zero_iff,hval] using hz₂ : False)

def Pair.toPick (p : Pair) : PickSum 2 where
  nonempty := by decide
  weight := ![p.a₁,p.a₂]
  location := ![p.w₁,p.w₂]
  pos := by intro i; fin_cases i <;> simp [p.ha₁,p.ha₂]
  below := by intro i; fin_cases i <;> simp [p.hw₁,p.hw₂]

theorem Pair.toPick_power (p : Pair) (ε : ℝ) : p.toPick.power (1+ε) = critical p ε := by
  funext z
  simp [PickSum.power,PickSum.value,Pair.toPick,critical,Pair.value,Fin.sum_univ_two]

theorem Pair.critical_domain (p : Pair) {ε : ℝ} (he : 0<ε) : p.quotientDomain ε := by
  have ht : 1 < 1+ε := by linarith
  simpa only [Pair.toPick_power,Pair.quotientDomain] using
    And.intro (p.toPick.power_memLp_two ht)
      (And.intro (p.toPick.log_power_memLp_two ht) (p.toPick.powerL2_norm_pos ht))

end Liu
