import Liu.GreenEstimates
import Liu.Source
import Liu.Projection

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate
namespace Liu

theorem inverse_distance_integrable (z : ℂ) (R : ℝ) :
    IntegrableOn (fun w : ℂ => ‖z-w‖⁻¹) (Metric.ball z R) volume := by
  have h := ((measurePreserving_add_right (volume:Measure ℂ) (-z)).integrableOn_comp_preimage
    ((Homeomorph.addRight (-z)).measurableEmbedding)).mpr (integrable_inverse_distance_ball R)
  have pre : (fun x : ℂ => x + -z) ⁻¹' Metric.ball 0 R = Metric.ball z R := by
    ext w; simp [Metric.mem_ball,dist_eq_norm,sub_eq_add_neg]
  rw [pre] at h
  simpa [Function.comp_def,←sub_eq_add_neg,norm_sub_rev z] using h

theorem greenLog_local_bound {z w : ℂ} (hz : 0≤z.im) (hw : 0<w.im) {R : ℝ} (hR : ‖w‖≤R) :
    |greenLog z w| ≤ (‖z‖+R)*‖z-w‖⁻¹ := by
  by_cases h : z = w
  · simp [greenLog,h]
  have hpos := greenLog_nonneg_le z w hz hw h
  rw [abs_of_nonneg hpos.1]
  have hden := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have hnum : z ≠ conj w := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi; linarith
  have hratio := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hnum)) hden
  calc
    _ ≤ ‖z-conj w‖ / ‖z-w‖ := (Real.log_le_sub_one_of_pos hratio).trans (by linarith)
    _ ≤ _ := by
      rw [div_eq_mul_inv]; gcongr
      exact (norm_sub_le ..).trans (by simpa using add_le_add_left hR ‖z‖)

theorem greenLog_far_bound {z w : ℂ} (hz : 0 < z.im) (hw : 0<w.im)
    (hf : max 1 (2*‖z‖) < ‖w‖) :
    |greenLog z w| ≤ 16*z.im / (1+‖w‖) := by
  have hw₁ := (le_max_left 1 (2*‖z‖)).trans_lt hf
  have hw₂ := (le_max_right 1 (2*‖z‖)).trans_lt hf
  have hne : z≠w := fun he => by rw [he] at hw₂; linarith [norm_nonneg w]
  obtain ⟨hpos,hhigh⟩ := greenLog_nonneg_le z w hz.le hw hne
  rw [abs_of_nonneg hpos]
  have hgap : ‖w‖/2 ≤ ‖z-w‖ := by
    have h := norm_add_le (w-z) z
    rw [sub_add_cancel,norm_sub_rev w z] at h
    linarith
  have hsq := pow_le_pow_left₀ (show 0 ≤ ‖w‖/2 by positivity) hgap 2
  have hw0 := (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  apply hhigh.trans
  apply (div_le_div_iff₀ (sq_pos_of_pos hw0) (by positivity)).mpr
  have him := Complex.im_le_norm w
  have ha : w.im*(1+‖w‖) ≤ ‖w‖*(1+‖w‖) := mul_le_mul_of_nonneg_right him (by positivity)
  have hb : ‖w‖ ≤ ‖w‖^2 := by nlinarith [mul_nonneg (norm_nonneg w) (sub_nonneg.mpr hw₁.le)]
  have hc : 2*(w.im*(1+‖w‖)) ≤ 16*‖z-w‖^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hc hz.le]

theorem PickSum.source_measurable {n : ℕ} (p : PickSum n) : Measurable (source p.value) := by
  have hm : Measurable p.value := by
    have h := p.power_measurable 1
    change Measurable (fun z => (p.value z)^((1:ℝ):ℂ)) at h
    simpa using h
  have hd := measurable_deriv p.value
  unfold source
  fun_prop

/-- Absolute convergence of the reflected Green integral for the actual Pick source
at each interior point of the half-plane. -/
theorem PickSum.potential_integrable {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun w => (greenLog z w:ℂ)*source p.value w) upperArea := by
  let R := max 1 (2*‖z‖)
  let L := p.derivativeBound/2
  have hL : 0 ≤ L := by
    dsimp [L,PickSum.derivativeBound]
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (p.pos i).le (sq_nonneg _)
  have hR : 0 ≤ R := le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left ..)
  let F := fun w : ℂ => (greenLog z w:ℂ)*source p.value w
  have hm : Measurable F := by
    have hs := p.source_measurable
    dsimp [F,greenLog]
    fun_prop
  let core := upper ∩ Metric.closedBall (0:ℂ) R
  let exterior := upper ∩ (Metric.closedBall (0:ℂ) R)ᶜ
  have hcore : IntegrableOn F core volume := by
    have localInt : IntegrableOn (fun w : ℂ => ((‖z‖+R)*L)*‖z-w‖⁻¹) (Metric.ball z (R+‖z‖+1)) volume := (inverse_distance_integrable z (R+‖z‖+1)).const_mul ((‖z‖+R)*L)
    have hsub : core ⊆ Metric.ball z (R+‖z‖+1) := by
      intro w hw
      have hwR : ‖w‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw.2
      rw [Metric.mem_ball,dist_eq_norm]
      linarith [norm_sub_le w z]
    apply (localInt.mono_set hsub).mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem (μ := volume) (upper_open.measurableSet.inter Metric.isClosed_closedBall.measurableSet)] with w hw
    have hwR : ‖w‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw.2
    have hker := greenLog_local_bound hz.le hw.1 hwR
    have hsrc := p.source_decay (le_of_lt hw.1)
    have hsrc' : ‖source p.value w‖ ≤ L := hsrc.trans
      (div_le_self hL (by nlinarith [norm_nonneg w,sq_nonneg ‖w‖]))
    change ‖(greenLog z w:ℂ)*source p.value w‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ ((‖z‖+R)*‖z-w‖⁻¹)*L := mul_le_mul hker hsrc' (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hout : IntegrableOn F exterior volume := by
    have hbr : (Module.finrank ℝ ℂ : ℝ) < 3 := by norm_num
    have hdom := (integrable_one_add_norm (μ := (volume:Measure ℂ)) hbr).const_mul (16*z.im*L)
    apply hdom.restrict.mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem (μ := volume)
      (upper_open.measurableSet.inter Metric.isClosed_closedBall.measurableSet.compl)] with w hw
    have hwR : R < ‖w‖ := lt_of_not_ge (fun h => hw.2 (by simpa only [Metric.mem_closedBall,dist_zero_right] using h))
    have hker := greenLog_far_bound hz hw.1 hwR
    have hsrc := p.source_decay (le_of_lt hw.1)
    change ‖(greenLog z w:ℂ)*source p.value w‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (16*z.im/(1+‖w‖))*(L/(1+‖w‖)^2) := mul_le_mul hker hsrc (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [Real.rpow_neg (by positivity : 0 ≤ 1+‖w‖),Real.rpow_ofNat]
        field_simp [show 1+‖w‖≠0 by positivity]
        <;> ring
  have all : IntegrableOn F upper volume := (hcore.union hout).mono_set (by
    intro w hw
    by_cases hh : w ∈ Metric.closedBall (0:ℂ) R
    · exact Or.inl ⟨hw,hh⟩
    · exact Or.inr ⟨hw,hh⟩)
  unfold upperArea area
  rw [Measure.restrict_smul]
  exact all.smul_measure ENNReal.ofReal_ne_top

end Liu
