module

public import Liu.BandSlices
public import Liu.FieldIncrement

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter Metric
open scoped Topology ComplexConjugate
namespace Liu

def bandPoint (y : ℝ) (z : ℂ) : ℂ := ⟨z.re,y*z.im⟩

private theorem bandPoint_form (y : ℝ) (z : ℂ) :
    bandPoint y z=(z.re:ℂ)+((y*z.im:ℝ):ℂ)*Complex.I := by
  apply Complex.ext <;> simp [bandPoint]

private theorem physicalDensity_measurable {S : ℂ → ℂ} (hs : Measurable S) :
    Measurable (physicalDensity S) := by
  have hf := field_measurable S
  unfold physicalDensity; fun_prop

/-- Horizontal sections throughout the first unit of height have a common
integrable envelope as the poles move farther from the boundary. -/
theorem PickSum.sampled_density_envelope {n : ℕ} (p : PickSum n) :
    ∃ E : ℝ → ℝ, Integrable E ∧ ∀ u : ℝ, 0≤u → ∀ h∈Icc (0:ℝ) 1, ∀ z∈depthBand 1,
    ‖physicalDensity (depthTranslate p.value u) (bandPoint h z)‖ ≤ E z.re := by
  obtain ⟨B,hB,HB⟩ := p.field_increment_weighted
  obtain ⟨H,hH,HH⟩ := p.depth_field_envelope
  have hk : 0≤k₀ := by unfold k₀; positivity
  have hp := p.bound_pos
  let K := 2*B^2+k₀*p.bound^2
  let E := fun x : ℝ => 2*H x^2+K*(1+‖x‖)^(-(2:ℝ))
  have hi := (integrable_one_add_norm (r:=2) (μ:=(volume:Measure ℝ)) (by norm_num)).const_mul K
  refine ⟨E,(hH.const_mul 2).add hi,?_⟩
  intro u hu h hh z hz
  let y := h*z.im
  have hy0 : 0≤y := mul_nonneg hh.1 (le_of_lt hz.1)
  have hy1 : y≤1 := (mul_le_mul hh.2 hz.2 (le_of_lt hz.1) zero_le_one).trans_eq (one_mul _)
  let a := 1+‖z.re‖
  have ha : 1≤a := by dsimp only [a]; linarith [norm_nonneg z.re]
  have hap := zero_lt_one.trans_le ha
  let S := depthTranslate p.value u
  have hinc := HB u hu (z.re:ℂ) (by simp) y hy0
  have hform : bandPoint h z=(z.re:ℂ)+(y:ℂ)*Complex.I := bandPoint_form h z
  rw [←hform,Complex.norm_real] at hinc
  have hsmall : ‖field S (bandPoint h z)-field S z.re‖≤B/a := hinc.trans (by
    change B*y^(3/4:ℝ)/a^(5/4:ℝ)≤B/a
    apply div_le_div₀ hB _ hap _
    · simpa using mul_le_mul_of_nonneg_left (rpow_le_one hy0 hy1 (by norm_num : (0:ℝ)≤3/4)) hB
    · simpa only [rpow_one] using rpow_le_rpow_of_exponent_le ha (by norm_num : (1:ℝ)≤5/4))
  have hv : ‖field S (bandPoint h z)‖≤H z.re+B/a := by
    have he := norm_sub_le_norm_sub_add_norm_sub (field S (bandPoint h z)) (field S z.re) 0
    simp only [sub_zero] at he
    linarith [HH u hu z.re]
  let v := bandPoint h z+(u:ℂ)*Complex.I
  have hy : 0≤v.im := by change 0≤(bandPoint h z+(u:ℂ)*Complex.I).im; simp [bandPoint]; linarith [show 0≤h*z.im from hy0]
  have hr : ‖z.re‖≤‖v‖ := by simpa [v,bandPoint,Real.norm_eq_abs] using Complex.abs_re_le_norm v
  have hS : ‖S (bandPoint h z)‖≤p.bound/a := (p.global_decay hy).trans (div_le_div_of_nonneg_left hp.le hap (add_le_add (le_refl _) hr))
  change ‖k₀*‖S (bandPoint h z)‖^2-‖field S (bandPoint h z)‖^2‖≤_
  apply (norm_sub_le ..).trans
  simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hk (sq_nonneg ‖S (bandPoint h z)‖)),abs_of_nonneg (sq_nonneg ‖field S (bandPoint h z)‖)]
  have hS' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hS 2) hk
  have hv' := pow_le_pow_left₀ (norm_nonneg _) hv 2
  change _≤2*H z.re^2+K*a^(-(2:ℝ))
  rw [rpow_neg hap.le,rpow_two]
  have eqn : 2*(B/a)^2+k₀*(p.bound/a)^2=K*(a^2)⁻¹ := by dsimp [K]; ring
  nlinarith only [hS',hv',sq_nonneg (H z.re-B/a),eqn]

private theorem sampled_eq {n : ℕ} (p : PickSum n) {u h : ℝ} (hu : 0≤u) (hh : 0<h)
    (hi : IntegrableOn (fun z => physicalDensity (depthTranslate p.value u) (bandPoint h z)) (depthBand 1) area) :
    (∫ z in depthBand h, physicalDensity (depthTranslate p.value u) z ∂area)/h =
      ∫ z in depthBand 1, physicalDensity (depthTranslate p.value u) (bandPoint h z) ∂area := by
  have hint := (p.deeper u hu).density_band_integrable h
  rw [p.deeper_value hu] at hint
  rw [integral_depthBand hh.le hint,integral_depthBand zero_le_one hi]
  let S := depthTranslate p.value u
  let f := fun y : ℝ => ∫ x : ℝ, physicalDensity S ⟨x,y⟩
  change (1/π)*(∫ y in 0..h,f y)/h=(1/π)*∫ y in 0..1, f (h*y)
  rw [intervalIntegral.integral_comp_mul_left f hh.ne',mul_zero,mul_one,smul_eq_mul]; ring

/-- The strip average tends to the negative boundary flux. The starting
translation is allowed to vary while the strip thickness tends to zero. -/
theorem PickSum.band_average_limit {n : ℕ} (p : PickSum n) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {u h : ι → ℝ} {a : ℝ} (ha : 0≤a) (hu : Tendsto u l (𝓝 a))
    (hh : Tendsto h l (𝓝 0)) (hp : ∀ᶠ i in l, 0≤u i ∧ 0<h i) :
    Tendsto (fun i => (∫ z in depthBand (h i),physicalDensity (depthTranslate p.value (u i)) z ∂area)/(h i))
      l (𝓝 (-boundaryFlux (depthTranslate p.value a))) := by
  let G := fun (b t : ℝ) (z : ℂ) => physicalDensity (depthTranslate p.value b) (bandPoint t z)
  obtain ⟨E,hE,he⟩ := p.sampled_density_envelope
  have hms (b t : ℝ) : Measurable (G b t) := by
    have hS : Measurable (depthTranslate p.value b) := by unfold depthTranslate PickSum.value pole; fun_prop
    exact (physicalDensity_measurable hS).comp (show Measurable (bandPoint t) by rw [show bandPoint t = fun z : ℂ => (z.re:ℂ)+((t*z.im:ℝ):ℂ)*Complex.I from funext (bandPoint_form t)]; fun_prop)
  have hEI : IntegrableOn (fun z : ℂ => E z.re) (depthBand 1) area := integrableOn_re_band hE 1
  have hsmall : ∀ᶠ i in l, 0≤u i ∧ h i∈Ioc (0:ℝ) 1 := by
    filter_upwards [hp,hh.eventually_lt_const zero_lt_one] with i H h1 using ⟨H.1,H.2,h1.le⟩
  have hlim : Tendsto (fun i => ∫ z in depthBand 1,G (u i) (h i) z ∂area) l
      (𝓝 (∫ z in depthBand 1,G a 0 z ∂area)) := by
    apply tendsto_integral_filter_of_dominated_convergence _ _ _ hEI _
    · exact Eventually.of_forall fun i => (hms ..).aestronglyMeasurable
    · filter_upwards [hsmall] with i H
      filter_upwards [ae_restrict_mem (μ:=area) (show MeasurableSet (depthBand 1) from measurableSet_Ioc.preimage Complex.measurable_im)] with z hz
      exact he _ H.1 _ ⟨H.2.1.le,H.2.2⟩ z hz
    · filter_upwards [ae_restrict_mem (μ:=area) (show MeasurableSet (depthBand 1) from measurableSet_Ioc.preimage Complex.measurable_im)] with z hz
      let x : ℂ := (z.re:ℂ)
      let y := fun i => h i*z.im
      have hy : Tendsto y l (𝓝 0) := by simpa [y] using hh.mul_const z.im
      have hu' : Tendsto u l (𝓝[Ici 0] a) := tendsto_nhdsWithin_iff.mpr ⟨hu,hp.mono fun i H => H.1⟩
      have hboundary := (p.depth_trace_continuous z.re a ha).tendsto.comp hu'
      obtain ⟨B,hB,H⟩ := p.field_increment_weighted
      have hδ : Tendsto (fun i => field (depthTranslate p.value (u i)) (bandPoint (h i) z)-
          field (depthTranslate p.value (u i)) x) l (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero' (g:=fun i => B*(y i)^(3/4:ℝ)/(1+‖x‖)^(5/4:ℝ)) (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
        · filter_upwards [hp] with i Hi
          rw [bandPoint_form]
          exact H (u i) Hi.1 x (by simp [x]) _ (mul_nonneg Hi.2.le (le_of_lt hz.1))
        · simpa using ((hy.rpow_const_nhds_zero (by norm_num : (0:ℝ)<3/4)).const_mul B).div_const ((1+‖x‖)^(5/4:ℝ))
      have hfield := hδ.add hboundary
      simp only [Function.comp_def,x,sub_add_cancel,zero_add] at hfield
      have harg : Tendsto (fun i => bandPoint (h i) z+(u i:ℂ)*Complex.I) l (𝓝 (x+(a:ℂ)*Complex.I)) := by
        simp only [bandPoint_form]
        have hyc := (Complex.continuous_ofReal.continuousAt.tendsto.comp hy).mul_const Complex.I
        simpa only [Function.comp_def,Complex.ofReal_zero,zero_mul,add_zero,y,x] using
          ((tendsto_const_nhds (x:=x)).add hyc).add ((Complex.continuous_ofReal.continuousAt.tendsto.comp hu).mul_const Complex.I)
      have hval := (p.hasDerivAt (show 0≤(x+(a:ℂ)*Complex.I).im by simpa [x] using ha)).continuousAt.tendsto.comp harg
      have H := ((hval.norm.pow 2).const_mul k₀).sub (hfield.norm.pow 2)
      simpa only [Function.comp_def,G,physicalDensity,depthTranslate,bandPoint_form,zero_mul,Complex.ofReal_zero,add_zero,x] using H
  have hI := integrableOn_band_of_envelope (hms a 0) hE (he a ha 0 (by constructor <;> norm_num))
  have hzero : (∫ z in depthBand 1,G a 0 z ∂area)= -boundaryFlux (depthTranslate p.value a) := by
    rw [integral_depthBand zero_le_one hI]
    change (1/π)*(∫ y in (0:ℝ)..1, ∫ x : ℝ, physicalDensity (depthTranslate p.value a) ⟨x,0*y⟩)=_
    simp only [zero_mul]
    simp only [intervalIntegral.integral_const,sub_zero,one_smul]
    unfold physicalDensity boundaryFlux
    rw [←neg_div,←integral_neg]; simp only [neg_sub]
    let S := depthTranslate p.value a
    change (1/π)*(∫ x : ℝ,k₀*‖S x‖^2-‖field S x‖^2)=(∫ x : ℝ,k₀*‖S x‖^2-‖field S x‖^2)/π
    ring
  rw [hzero] at hlim
  apply hlim.congr'
  filter_upwards [hsmall] with i H
  exact (sampled_eq p H.1 H.2.1 (integrableOn_band_of_envelope (hms ..) hE (he _ H.1 _ ⟨H.2.1.le,H.2.2⟩))).symm

end Liu
