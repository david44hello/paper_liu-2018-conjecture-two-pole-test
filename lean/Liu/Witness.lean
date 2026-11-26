import Liu.Denominator
import Liu.Source

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu

def isWitness (W : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ W upper ∧ ContinuousOn W {z : ℂ | 0 ≤ z.im} ∧
    ∃ C > 0, ∃ R > 0, ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ →
      ‖W z - (Real.pi/2:ℝ)‖ ≤ C*(1+Real.log ‖z‖)/‖z‖

def optimalWitness (S : ℂ → ℂ) (z : ℂ) : ℂ :=
  (S z*(Complex.arg (S z):ℂ)-field S z)/S z

def witnessDifference (S W : ℂ → ℂ) (z : ℂ) := S z * (W z - optimalWitness S z)

def truncatedWitness (S W : ℂ → ℂ) (R : ℝ) : ℝ :=
  ∫ z in halfDisc R, k₀*‖S z‖^2 - ‖S z‖^2*‖(Complex.arg (S z):ℂ)-W z‖^2 ∂area

theorem halfDisc_integral_limit {f : ℂ → ℝ} (hf : Integrable f upperArea) :
    Tendsto (fun R : ℝ => ∫ z in halfDisc R, f z ∂area) atTop (𝓝 (∫ z, f z ∂upperArea)) := by
  have hU : (⋃ R : ℝ, halfDisc R) = upper := by
    ext z
    constructor
    · intro h
      obtain ⟨R,h⟩ := mem_iUnion.mp h
      exact h.1
    · intro h
      exact mem_iUnion.mpr ⟨‖z‖+1,h,by simp⟩
  have hi : IntegrableOn f (⋃ R : ℝ, halfDisc R) area := hU.symm ▸ hf
  simpa only [hU,upperArea] using tendsto_setIntegral_of_monotone (s:=halfDisc)
    (fun R : ℝ => upper_open.measurableSet.inter (Metric.isOpen_ball (x:=0) (ε:=R)).measurableSet)
    (show Monotone halfDisc from fun _ _ h => inter_subset_inter_right _ (Metric.ball_subset_ball h)) hi

private theorem witness_point_identity {S W : ℂ → ℂ} {z : ℂ} (hz : S z ≠ 0) :
    k₀*‖S z‖^2-‖S z‖^2*‖(Complex.arg (S z):ℂ)-W z‖^2 =
      (k₀*‖S z‖^2-‖field S z‖^2) + 2*(field S z*conj (witnessDifference S W z)).re -
      ‖witnessDifference S W z‖^2 := by
  have heq : S z*((Complex.arg (S z):ℂ)-W z) = field S z - witnessDifference S W z := by
    unfold witnessDifference optimalWitness
    field_simp [hz]
    <;> ring
  rw [←mul_pow,←norm_mul,heq]
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

/-- The exact witness finite-part identity of 4.3 follows from the integrable
orthogonality in 4.2 and the finite part in 2.5, applied to the actual fields. -/
theorem witness_limit_of_orthogonality {n : ℕ} (p : PickSum n) (W : ℂ → ℂ)
    (hf : finitePartExists p.value) (hg : MemLp (witnessDifference p.value W) 2 upperArea)
    (hcross : Integrable (fun z => field p.value z*conj (witnessDifference p.value W z)) upperArea)
    (horth : (∫ z, field p.value z*conj (witnessDifference p.value W z) ∂upperArea) = 0) :
    Tendsto (truncatedWitness p.value W) atTop
      (𝓝 (deficit p.value - energy (witnessDifference p.value W))) := by
  let g := witnessDifference p.value W
  let c := fun z => (field p.value z*conj (g z)).re
  have hc : Integrable c upperArea := Complex.reCLM.integrable_comp hcross
  have hzero : ∫ z, c z ∂upperArea = 0 := by
    change ∫ z, (field p.value z*conj (g z)).re ∂upperArea = _
    exact (integral_re hcross).trans (by rw [horth]; rfl)
  have hg2 : Integrable (fun z => ‖g z‖^2) upperArea :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have heq (R : ℝ) (hR : 0 < R) : truncatedWitness p.value W R =
      truncatedDeficit p.value R + 2*(∫ z in halfDisc R, c z ∂area) -
      ∫ z in halfDisc R, ‖g z‖^2 ∂area := by
    have hc' := (show IntegrableOn c upper area from hc).mono_set (inter_subset_left (t:=Metric.ball 0 R))
    have hg' := (show IntegrableOn (fun z => ‖g z‖^2) upper area from hg2).mono_set (inter_subset_left (t:=Metric.ball 0 R))
    have hab : IntegrableOn (fun z => k₀*‖p.value z‖^2-‖field p.value z‖^2+2*c z) (halfDisc R) area := (hf.1 R hR).add (hc'.const_mul 2)
    unfold truncatedWitness truncatedDeficit
    rw [←integral_const_mul,←integral_add (hf.1 R hR) (hc'.const_mul 2),
      ←integral_sub hab hg']
    apply setIntegral_congr_fun (upper_open.measurableSet.inter Metric.isOpen_ball.measurableSet)
    intro z hz
    apply witness_point_identity
    intro he
    have h := p.value_im_pos (le_of_lt hz.1)
    simp [he] at h
  have H := ((finite_part_limit hf).add ((halfDisc_integral_limit hc).const_mul 2)).sub
    (halfDisc_integral_limit hg2)
  rw [hzero,mul_zero,add_zero,←energy_eq_integral hg] at H
  exact H.congr' ((eventually_gt_atTop (0:ℝ)).mono fun R hR => (heq R hR).symm)

end Liu
