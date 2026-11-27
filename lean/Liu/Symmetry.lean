module

public import Liu.FinitePart
public import Liu.GreenBoundary

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace Liu

theorem source_mass_scale (S : ℂ → ℂ) (c : ℝ) (z : ℂ) :
    source (fun w => (c:ℂ)*S w) z = (c:ℂ)*source S z := by
  by_cases hc : c = 0
  · simp [hc,source]
  simp only [source,deriv_const_mul_field,map_mul,Complex.conj_ofReal]
  rw [mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hc)]
  ring

theorem potential_mass_scale (S : ℂ → ℂ) (c : ℝ) :
    potential (fun z => (c:ℂ)*S z) = fun z => (c:ℂ)*potential S z := by
  funext z
  unfold potential
  simp_rw [source_mass_scale,mul_left_comm _ (c:ℂ),integral_const_mul]

theorem field_mass_scale (S : ℂ → ℂ) (c : ℝ) (z : ℂ) :
    field (fun w => (c:ℂ)*S w) z = (c:ℂ)*field S z := by
  have h := congrFun (fderiv_const_smul_field (𝕜:=ℝ) (f:=potential S) (c:ℂ)) z
  change fderiv ℝ (fun w => (c:ℂ)*potential S w) z = (c:ℂ) • fderiv ℝ (potential S) z at h
  simp only [field,potential_mass_scale,h,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem truncatedDeficit_mass_scale (S : ℂ → ℂ) (c R : ℝ) :
    truncatedDeficit (fun w => (c:ℂ)*S w) R = c^2*truncatedDeficit S R := by
  unfold truncatedDeficit
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  rw [field_mass_scale,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  simp only [mul_pow,sq_abs]
  ring

theorem deficit_mass_scale {S : ℂ → ℂ} (hf : finitePartExists S) (c : ℝ) :
    deficit (fun w => (c:ℂ)*S w) = c^2 * deficit S := by
  apply Tendsto.limUnder_eq
  change Tendsto (fun R => truncatedDeficit (fun w => (c:ℂ)*S w) R) atTop _
  simpa only [truncatedDeficit_mass_scale] using
    (show Tendsto (fun R => c^2 * truncatedDeficit S R) atTop (𝓝 (c^2*deficit S)) from
      (finite_part_limit hf).const_mul (c^2))

theorem Pair.scaleMass_value (p : Pair) (c : ℝ) (hc : 0<c) :
    (p.scaleMass c hc).value = fun z => (c:ℂ)*p.value z := by
  funext z
  simp [Pair.scaleMass,Pair.value,pole]
  ring

theorem Pair.scaleMass_deficit (p : Pair) (hf : finitePartExists p.value) (c : ℝ) (hc : 0<c) :
    deficit (p.scaleMass c hc).value = c^2*deficit p.value := by
  rw [p.scaleMass_value c hc,deficit_mass_scale hf]

theorem source_shift (S : ℂ → ℂ) (x : ℝ) (z : ℂ) :
    source (fun w => S (w+(x:ℂ))) z = source S (z+(x:ℂ)) := by
  simp [source,deriv_comp_add_const]

theorem potential_shift (S : ℂ → ℂ) (x : ℝ) :
    potential (fun w => S (w+(x:ℂ))) = fun z => potential S (z+(x:ℂ)) := by
  funext z
  let e := Homeomorph.addRight (x:ℂ)
  have hv := (measurePreserving_add_right (volume:Measure ℂ) (x:ℂ)).setIntegral_preimage_emb
    e.measurableEmbedding (fun w : ℂ => (greenLog (z+x) w:ℂ)*source S w) upper
  have he : (fun w : ℂ => w+(x:ℂ)) ⁻¹' upper = upper := by ext w; simp [upper]
  rw [he] at hv
  have ker (w : ℂ) : greenLog (z+x) (w+x) = greenLog z w := by simp [greenLog]
  simp only [ker] at hv
  unfold potential area
  simp only [Measure.restrict_smul,integral_smul_measure,source_shift]
  exact congrArg _ hv

theorem field_shift (S : ℂ → ℂ) (x : ℝ) (z : ℂ) :
    field (fun w => S (w+(x:ℂ))) z = field S (z+(x:ℂ)) := by
  simp only [field,potential_shift,fderiv_comp_add_right]

end Liu
