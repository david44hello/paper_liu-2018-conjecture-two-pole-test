import Liu.Potential

noncomputable section
open Set MeasureTheory Real Filter
open scoped ComplexConjugate Topology
namespace Liu

/-- Reflect the observation point across the real axis. This gives a bound linear
in its height, with only an integrable first-order singularity at the source. -/
theorem greenLog_height_bound {z w : ℂ} (hz : 0 ≤ z.im) (hw : 0 < w.im) :
    |greenLog z w| ≤ 2*z.im*‖z-w‖⁻¹ := by
  by_cases h : z = w
  · simp [h,greenLog]
  have hp := (greenLog_nonneg_le z w hz hw h).1
  have hd := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have hne : z ≠ conj w := fun he => by
    have hh := congrArg Complex.im he
    simp at hh; linarith
  have hn := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have href : ‖z-conj w‖ = ‖conj z-w‖ := by
    have e := Complex.norm_conj (z-conj w)
    simpa using e.symm
  have him : conj z-z = (-2*z.im:ℝ)*Complex.I := by apply Complex.ext <;> simp <;> ring
  have gap : ‖z-conj w‖ ≤ 2*z.im+‖z-w‖ := by
    rw [href]
    have hh := norm_add_le (conj z-z) (z-w)
    rw [sub_add_sub_cancel,him,norm_mul,Complex.norm_I,mul_one] at hh
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg hz] using hh
  rw [abs_of_nonneg hp]
  apply (Real.log_le_sub_one_of_pos (div_pos hn hd)).trans
  rw [← div_eq_mul_inv,sub_le_iff_le_add]
  apply (div_le_iff₀ hd).mpr
  rw [add_mul,div_mul_cancel₀ _ hd.ne',one_mul]
  exact gap

theorem potential_boundary (S : ℂ → ℂ) (x : ℝ) : potential S x = 0 := by
  unfold potential
  have ht : ∀ w ∈ upper, (greenLog x w : ℂ) * source S w = 0 := by
    intro w hw
    have hh := greenLog_height_bound (z := (x:ℂ)) (by simp) hw
    have hg : greenLog x w = 0 := abs_nonpos_iff.mp (by simpa using hh)
    simp [hg]
  exact setIntegral_eq_zero_of_forall_eq_zero ht

def localInverse (z : ℂ) (w : ℂ) : ℝ :=
  (Metric.ball z 1).indicator (fun v => ‖z-v‖⁻¹) w

theorem localInverse_integrable (z : ℂ) : Integrable (localInverse z) volume :=
  (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr (inverse_distance_integrable z 1)

theorem localInverse_integral (z : ℂ) :
    ∫ w, localInverse z w = ∫ w, localInverse 0 w := by
  let e := Homeomorph.addRight (-z)
  have h := (measurePreserving_add_right (volume:Measure ℂ) (-z)).integral_comp
    e.measurableEmbedding (localInverse 0)
  convert h using 1
  apply integral_congr_ae
  filter_upwards with w
  have hnear : w + -z ∈ Metric.ball (0:ℂ) 1 ↔ w ∈ Metric.ball z 1 := by
    simp [Metric.mem_ball,dist_eq_norm,sub_eq_add_neg]
  by_cases hw : w ∈ Metric.ball z 1
  · simp only [localInverse,indicator_of_mem hw,indicator_of_mem (hnear.mpr hw),zero_sub,norm_neg]
    rw [←sub_eq_add_neg,norm_sub_rev]
  · simp only [localInverse,indicator_of_notMem hw,indicator_of_notMem (mt hnear.mp hw)]
/-- Uniform boundary estimate on a bounded portion of the closed half-plane.
In particular the real boundary values of the Green integral are limits from inside. -/
theorem PickSum.potential_height_estimate {n : ℕ} (p : PickSum n) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C ≥ 0, ∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ T → ‖potential p.value z‖ ≤ C*z.im := by
  classical
  let L := p.derivativeBound/2
  have hL : 0 ≤ L := by
    have hg := p.source_decay (z:=0) (by simp)
    simpa [L] using (norm_nonneg _).trans hg
  let tail := fun w : ℂ => (1+‖w‖)^(-(3:ℝ))
  have hint : Integrable tail volume := integrable_one_add_norm (by norm_num)
  let A := ∫ w, localInverse 0 w
  let B := ∫ w, tail w
  have hA : 0 ≤ A := integral_nonneg fun w => indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _
  have hB : 0 ≤ B := integral_nonneg fun w => rpow_nonneg (by positivity) _
  refine ⟨(1/π)*(2*L)*(A+(2+T)*B),by positivity,?_⟩
  intro z hz hzT
  let g := fun w : ℂ => (2*z.im*L)*(localInverse z w + (2+T)*tail w)
  have hg : Integrable g volume :=
    ((localInverse_integrable z).add (hint.const_mul (2+T))).const_mul _
  have hgi : ∫ w, g w = (2*z.im*L)*(A+(2+T)*B) := by
    simp only [g,integral_const_mul,integral_add (localInverse_integrable z) (hint.const_mul (2+T)),
      localInverse_integral z,A,B]
  have gb (w : ℂ) : 0 ≤ g w := by
    have hi : 0 ≤ localInverse z w := indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _
    have ht : 0 ≤ tail w := rpow_nonneg (by positivity) _
    dsimp [g]; positivity
  let f := fun w : ℂ => (greenLog z w:ℂ)*source p.value w
  have hb : ‖∫ w, upper.indicator f w‖ ≤ (2*z.im*L)*(A+(2+T)*B) := by
    rw [← hgi]
    apply norm_integral_le_of_norm_le hg
    filter_upwards with w
    by_cases hw : w ∈ upper
    · rw [indicator_of_mem hw]
      have hk := greenLog_height_bound hz hw
      have hs := p.source_decay (le_of_lt hw)
      have hraw := mul_le_mul hk hs (norm_nonneg _) (by positivity : 0 ≤ 2*z.im*‖z-w‖⁻¹)
      change ‖(greenLog z w:ℂ)*source p.value w‖ ≤ _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply hraw.trans
      have hden : 0 < 1+‖w‖ := by positivity
      have ht : 0 ≤ tail w := rpow_nonneg hden.le _
      by_cases near : w ∈ Metric.ball z 1
      · have hsmall : L/(1+‖w‖)^2 ≤ L := div_le_self hL (by nlinarith [sq_nonneg ‖w‖,norm_nonneg w])
        have hm := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ 2*z.im*‖z-w‖⁻¹)
        simp only [g,localInverse,indicator_of_mem near]
        apply hm.trans
        rw [mul_right_comm (2*z.im) _ L]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_add_of_nonneg_right (mul_nonneg (by linarith) ht)
      · have hd : 1 ≤ ‖z-w‖ := by simpa [Metric.mem_ball,dist_eq_norm,norm_sub_rev w z] using near
        have hd0 : 0 < ‖z-w‖ := zero_lt_one.trans_le hd
        have tri : ‖w‖ ≤ ‖z-w‖+‖z‖ := by simpa [norm_sub_rev w z] using norm_add_le (w-z) z
        have hgeom : 1+‖w‖ ≤ (2+T)*‖z-w‖ := by nlinarith [mul_nonneg hT (sub_nonneg.mpr hd)]
        have ratio : ‖z-w‖⁻¹/(1+‖w‖)^2 ≤ (2+T)*tail w := by
          simp only [tail,rpow_neg hden.le,rpow_ofNat]
          field_simp [hd0.ne',hden.ne']
          <;> nlinarith [mul_le_mul_of_nonneg_right hgeom (sq_nonneg (1+‖w‖))]
        simp only [g,localInverse,indicator_of_notMem near,zero_add]
        calc
          _ = (2*z.im*L)*(‖z-w‖⁻¹/(1+‖w‖)^2) := by dsimp [L]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left ratio (by positivity)
    · simpa [hw] using gb w
  unfold potential area
  rw [Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/π)]
  have hvol : ‖∫ w in upper, f w‖ ≤ (2*z.im*L)*(A+(2+T)*B) := by
    rw [← integral_indicator upper_open.measurableSet]; exact hb
  calc
    _ ≤ (1/π)*((2*z.im*L)*(A+(2+T)*B)) := mul_le_mul_of_nonneg_left hvol (by positivity)
    _ = _ := by ring

theorem PickSum.potential_continuousAt_boundary {n : ℕ} (p : PickSum n) (x : ℝ) :
    ContinuousWithinAt (potential p.value) {z : ℂ | 0 ≤ z.im} (x:ℂ) := by
  let T := ‖(x:ℂ)‖+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨C,_,hC⟩ := p.potential_height_estimate hT
  unfold ContinuousWithinAt
  rw [potential_boundary]
  have htop : Tendsto (fun z : ℂ => z) (𝓝[{z : ℂ | 0 ≤ z.im}] (x:ℂ)) (𝓝 (x:ℂ)) :=
    nhdsWithin_le_nhds
  have hi := Complex.continuous_im.continuousAt.tendsto.comp htop
  have hr := continuous_norm.continuousAt.tendsto.comp htop
  have hs := hr.eventually_lt_const (show ‖(x:ℂ)‖ < T by dsimp [T]; linarith)
  apply squeeze_zero_norm' (a := fun z : ℂ => C*z.im) _ (by simpa using hi.const_mul C)
  filter_upwards [self_mem_nhdsWithin (a := (x:ℂ)) (s := {z : ℂ | 0 ≤ z.im}),hs] with z hz ht
  exact hC z hz (le_of_lt ht)

end Liu
