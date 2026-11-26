import Liu.Witness

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu

/-- An L²-continuous witness difference of zero energy vanishes at every point
of the open half-plane since normalized area is positive on open discs. -/
theorem witness_equality_iff {n : ℕ} (p : PickSum n) (W : ℂ → ℂ)
    (hW : ContinuousOn W upper) (hopt : ContinuousOn (optimalWitness p.value) upper)
    (hg : MemLp (witnessDifference p.value W) 2 upperArea) :
    energy (witnessDifference p.value W) = 0 ↔ EqOn W (optimalWitness p.value) upper := by
  let g := witnessDifference p.value W
  have hi : Integrable (fun z => ‖g z‖^2) upperArea :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  rw [energy_eq_integral hg]
  constructor
  · intro he
    have hzero := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖g z‖) hi).mp he
    have hw : W =ᵐ[upperArea] optimalWitness p.value := by
      filter_upwards [hzero,ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz hu
      have hval : p.value z≠0 := fun he => by have hh := p.value_im_pos (le_of_lt hu); simp [he] at hh
      change ‖g z‖^2=0 at hz
      have hgz : g z=0 := norm_eq_zero.mp ((pow_eq_zero_iff (by decide : 2≠0)).mp hz)
      exact sub_eq_zero.mp ((mul_eq_zero.mp hgz).resolve_left hval)
    unfold upperArea area at hw
    rw [Measure.restrict_smul] at hw
    have hv := (Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : (0:ℝ)<1/Real.pi))).mp hw
    exact Measure.eqOn_open_of_ae_eq hv upper_open hW hopt
  · intro he
    apply (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖g z‖) hi).mpr
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    simp [g,witnessDifference,he hz]

theorem witness_deficit_lower {n : ℕ} (p : PickSum n) (W : ℂ → ℂ)
    (hf : finitePartExists p.value) (hg : MemLp (witnessDifference p.value W) 2 upperArea)
    (hcross : Integrable (fun z => field p.value z*conj (witnessDifference p.value W z)) upperArea)
    (horth : (∫ z, field p.value z*conj (witnessDifference p.value W z) ∂upperArea) = 0)
    (hW : ContinuousOn W upper) (hopt : ContinuousOn (optimalWitness p.value) upper) :
    let L := limUnder atTop (truncatedWitness p.value W)
    L ≤ deficit p.value ∧ (L = deficit p.value ↔ EqOn W (optimalWitness p.value) upper) := by
  dsimp only
  rw [(witness_limit_of_orthogonality p W hf hg hcross horth).limUnder_eq]
  refine ⟨sub_le_self _ (sq_nonneg _),?_⟩
  rw [sub_eq_self,witness_equality_iff p W hW hopt hg]

end Liu
