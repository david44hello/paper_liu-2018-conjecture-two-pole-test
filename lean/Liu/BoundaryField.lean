import Liu.TraceIntegral

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology ComplexConjugate
namespace Liu

/-- The upward normal derivative in normalized half-plane area. -/
def poissonTrace (S : ℂ → ℂ) (x : ℝ) : ℂ :=
  ∫ w in upper, ((2*w.im/‖w-(x:ℂ)‖^2:ℝ):ℂ)*source S w ∂area

theorem poissonTrace_translated (S : ℂ → ℂ) (x : ℝ) :
    poissonTrace S x = ∫ v, boundaryTraceIntegrand (source S) x v ∂area := by
  classical
  have hv := measurePreserving_add_left (volume:Measure ℂ) (x:ℂ)
  have h : MeasurePreserving (fun v : ℂ => (x:ℂ)+v) area area :=
    ⟨hv.measurable,by unfold area; rw [Measure.map_smul _ hv.measurable.aemeasurable,hv.map_eq]⟩
  unfold poissonTrace
  rw [←integral_indicator upper_open.measurableSet,← h.integral_comp (Homeomorph.addLeft (x:ℂ)).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with v
  by_cases hv : 0 < v.im
  · have hu : (x:ℂ)+v ∈ upper := by simpa [upper] using hv
    simp [boundaryTraceIntegrand,hv,hu]
  · have hu : (x:ℂ)+v ∉ upper := by simpa [upper] using hv
    simp [boundaryTraceIntegrand,hv,hu]

theorem greenLog_reflect_observation (z w : ℂ) :
    greenLog (conj z) w = - greenLog z w := by
  have h₁ : ‖conj z-conj w‖ = ‖z-w‖ := by rw [←map_sub,Complex.norm_conj]
  have h₂ : ‖conj z-w‖ = ‖z-conj w‖ := by simpa using Complex.norm_conj (z-conj w)
  simp only [greenLog,h₁,h₂,←Real.log_inv,inv_div]

theorem potential_reflect_observation (S : ℂ → ℂ) (z : ℂ) :
    potential S (conj z) = -potential S z := by
  change (∫ w in upper, (greenLog (conj z) w:ℂ)*source S w ∂area) =
    -(∫ w in upper, (greenLog z w:ℂ)*source S w ∂area)
  simp_rw [greenLog_reflect_observation,Complex.ofReal_neg,neg_mul,integral_neg]

/-- Odd reflection and the unrestricted nontangential *and tangential* upper-half-plane
quotient limit give a full, two-real-variable Fréchet derivative at the boundary. -/
theorem boundary_derivative_of_quotient {F : ℂ → ℂ} {A : ℂ} (x : ℝ)
    (hodd : ∀ z, F (conj z) = -F z) (hzero : ∀ t : ℝ, F t = 0)
    (hq : Tendsto (fun z : ℂ => F z/(z.im:ℂ)) (𝓝[upper] (x:ℂ)) (𝓝 A)) :
    HasFDerivAt F (Complex.imCLM.smulRight A) (x:ℂ) := by
  rw [hasFDerivAt_iff_tendsto,Metric.tendsto_nhds_nhds]
  intro η hη
  obtain ⟨r,hr,hh⟩ := Metric.tendsto_nhdsWithin_nhds.mp hq η hη
  refine ⟨r,hr,?_⟩
  intro z hz
  simp only [hzero,sub_zero,ContinuousLinearMap.smulRight_apply,Complex.imCLM_apply,
    Complex.sub_im,Complex.ofReal_im,Complex.real_smul,Real.dist_eq,sub_zero,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))]
  by_cases h : z.im = 0
  · have heq : z = (z.re:ℂ) := by apply Complex.ext <;> simp [h]
    rw [h,Complex.ofReal_zero,zero_mul,sub_zero,heq,hzero,norm_zero,mul_zero]
    exact hη
  have distQ : ‖F z/(z.im:ℂ)-A‖ < η := by
    by_cases hu : 0 < z.im
    · simpa only [dist_eq_norm] using hh (show z ∈ upper from hu) hz
    · have hn : conj z ∈ upper := by change 0 < (conj z).im; simp; exact lt_of_le_of_ne (le_of_not_gt hu) h
      have heq : dist (conj z) (x:ℂ) = dist z (x:ℂ) := by
        rw [dist_eq_norm,dist_eq_norm]
        simpa using Complex.norm_conj (z-(x:ℂ))
      have hh' := hh hn (heq ▸ hz)
      simpa only [dist_eq_norm,hodd,Complex.conj_im,Complex.ofReal_neg,neg_div_neg_eq] using hh'
  have hx : ‖(z.im:ℂ)‖ ≤ ‖z-(x:ℂ)‖ := by
    simpa [Complex.norm_real,Real.norm_eq_abs] using Complex.abs_im_le_norm (z-(x:ℂ))
  have hden := norm_pos_iff.mpr (show z-(x:ℂ)≠0 from sub_ne_zero.mpr (fun e => h (by simp [e])))
  have hid : F z - (z.im:ℂ)*A = (z.im:ℂ)*(F z/(z.im:ℂ)-A) := by
    field_simp [Complex.ofReal_ne_zero.mpr h]
  rw [hid,norm_mul,←mul_assoc]
  apply lt_of_le_of_lt _ distQ
  exact mul_le_of_le_one_left (norm_nonneg _) (by
    rw [←div_eq_inv_mul]
    exact (div_le_one hden).mpr hx)

theorem PickSum.potential_hasFDerivAt_boundary {n : ℕ} (p : PickSum n) (x : ℝ) :
    HasFDerivAt (potential p.value) (Complex.imCLM.smulRight (poissonTrace p.value x)) (x:ℂ) := by
  apply boundary_derivative_of_quotient x (potential_reflect_observation p.value) (potential_boundary p.value)
  rw [poissonTrace_translated]
  exact p.potential_normal_quotient x

theorem PickSum.field_on_boundary {n : ℕ} (p : PickSum n) (x : ℝ) :
    field p.value x = Complex.I*poissonTrace p.value x := by
  simp [field,(p.potential_hasFDerivAt_boundary x).fderiv]

end Liu
