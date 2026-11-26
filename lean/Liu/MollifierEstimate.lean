import Liu.Denominator
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace Liu

theorem lp_two_integral_sq {μ : Measure ℂ} {f : ℂ → ℂ} (hf : MemLp f 2 μ) :
    (∫ z, ‖f z‖^2 ∂μ)=‖hf.toLp f‖^2 := by
  have hn : 0≤∫ z, ‖f z‖^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hn _),←Real.sqrt_eq_rpow,Real.sq_sqrt hn]

private theorem prob_jensen_square {ν : Measure ℂ} [IsProbabilityMeasure ν]
    {g : ℂ → ℂ} (hg : MemLp g 2 ν) : ‖∫ t, g t ∂ν‖^2≤∫ t, ‖g t‖^2 ∂ν := by
  have hi := hg.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hs := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2).trans
    ((convexOn_pow (𝕜:=ℝ) 2).map_integral_le (by fun_prop) isClosed_Ici
      (ae_of_all _ fun t => norm_nonneg (g t)) hi.norm hs)

/-- Average translates in any probability measure supported on shifts whose
L² distance from the original is at most ε. The same bound holds for the
distance of the average itself. -/
theorem average_translates_square {ν : Measure ℂ} [IsProbabilityMeasure ν]
    {f : ℂ → ℂ} (hf : Measurable f) (h₂ : MemLp f 2 volume) {ε : ℝ}
    (hbound : ∀ᵐ t ∂ν, (∫ z, ‖f (z-t)-f z‖^2)≤ε^2) :
    let D := fun z => (∫ t, f (z-t) ∂ν)-f z
    Integrable (fun z => ‖D z‖^2) volume ∧ (∫ z, ‖D z‖^2)≤ε^2 := by
  let b := fun q : ℂ × ℂ => f (q.1-q.2)-f q.1
  have hb : Measurable b := by dsimp [b]; fun_prop
  have hs : Measurable (fun q => ‖b q‖^2) := hb.norm.pow_const _
  have hshift (t : ℂ) : MemLp (fun z => b (z,t)) 2 volume := by
    exact (h₂.comp_measurePreserving (measurePreserving_sub_right (volume:Measure ℂ) t)).sub h₂
  have hi (t : ℂ) : Integrable (fun z => ‖b (z,t)‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (hshift t).aestronglyMeasurable).mp (hshift t)
  have hh : Integrable (fun q => ‖b q‖^2) (volume.prod ν) := by
    apply (integrable_prod_iff' hs.aestronglyMeasurable).mpr
    refine ⟨.of_forall hi,(integrable_const (ε^2)).mono' ?_ ?_⟩
    · exact (hs.stronglyMeasurable.norm.integral_prod_left').aestronglyMeasurable
    · filter_upwards [hbound] with t ht
      simp only [Real.norm_eq_abs,abs_pow,abs_of_nonneg (norm_nonneg _)]
      rw [abs_of_nonneg (integral_nonneg fun x : ℂ => sq_nonneg ‖b (x,t)‖)]
      exact ht
  have hm : StronglyMeasurable (fun z => ∫ t, f (z-t) ∂ν) :=
    (show Measurable (fun q : ℂ × ℂ => f (q.1-q.2)) by fun_prop).stronglyMeasurable.integral_prod_right'
  have hD : Measurable (fun z => ‖(∫ t, f (z-t) ∂ν)-f z‖^2) := (hm.measurable.sub hf).norm.pow_const _
  have hle : ∀ᵐ z, ‖(∫ t, f (z-t) ∂ν)-f z‖^2 ≤ ∫ t, ‖b (z,t)‖^2 ∂ν := by
    filter_upwards [hh.prod_right_ae] with z hz
    have hmz : MemLp (fun t => b (z,t)) 2 ν :=
      (memLp_two_iff_integrable_sq_norm ((hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mpr hz
    have hI := (hmz.integrable (by norm_num : (1:ℝ≥0∞)≤2)).add (integrable_const (f z))
    have eq : ∀ t, b (z,t)+f z=f (z-t) := by intro t; exact sub_add_cancel .. 
    have hi' : Integrable (fun t => f (z-t)) ν := hI.congr (.of_forall eq)
    have H := prob_jensen_square hmz
    change ‖∫ t, f (z-t)-f z ∂ν‖^2≤_ at H
    simpa only [integral_sub hi' (integrable_const _),integral_const,probReal_univ,one_smul] using H
  have hint := hh.integral_prod_left.mono' hD.aestronglyMeasurable
    (hle.mono fun z hz => by simpa only [Real.norm_eq_abs,abs_pow,abs_of_nonneg (norm_nonneg _)] using hz)
  refine ⟨hint,(integral_mono_ae hint hh.integral_prod_left hle).trans ?_⟩
  rw [←integral_prod _ hh,integral_prod_symm _ hh]
  exact (integral_mono_ae hh.integral_prod_right (integrable_const (ε^2)) hbound).trans_eq (by simp)

theorem small_shift_energy {f : ℂ → ℂ} (hf : MemLp f 2 volume) {ε : ℝ} (he : 0<ε) :
    ∃ r>0, ∀ t : ℂ, ‖t‖<r → (∫ z, ‖f (z-t)-f z‖^2)≤ε^2 := by
  letI : Fact ((2:ℝ≥0∞)≠∞) := ⟨by norm_num⟩
  let u := hf.toLp f
  let S := fun t : ℂ => DomAddAct.mk (-t) +ᵥ u
  have hC : Continuous S := (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const
  have h₀ : S 0=u := by simp [S]
  have hn : ∀ᶠ t in 𝓝 (0:ℂ), ‖S t-u‖<ε := by
    have H : Tendsto (fun t => ‖S t-u‖) (𝓝 0) (𝓝 ‖S 0-u‖) := (hC.sub (continuous_const (y:=u))).norm.tendsto _
    rw [h₀,sub_self,norm_zero] at H
    exact H.eventually (Iio_mem_nhds he)
  obtain ⟨r,hr,hh⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r,hr,fun t ht => ?_⟩
  have ht' := hh (show t∈ball (0:ℂ) r by simpa using ht)
  have hs := hf.comp_measurePreserving (measurePreserving_add_left (volume:Measure ℂ) (-t))
  have eq := lp_two_integral_sq (hs.sub hf)
  change (∫ z, ‖f (-t+z)-f z‖^2)=‖(hs.sub hf).toLp _‖^2 at eq
  rw [MemLp.toLp_sub hs hf] at eq
  calc
    _ = ∫ z, ‖f (-t+z)-f z‖^2 := by simp only [sub_eq_add_neg,add_comm]
    _ = ‖S t-u‖^2 := eq
    _ ≤ ε^2 := pow_le_pow_left₀ (norm_nonneg _) (le_of_lt ht') 2

end Liu
