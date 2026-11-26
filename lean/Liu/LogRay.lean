import Liu.GreenRadialWeights
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

private theorem ray_slit {a : ℂ} (ha : a ∈ Complex.slitPlane) {t : ℝ} (ht : 0≤t) :
    1+(t:ℂ)*a ∈ Complex.slitPlane := by
  rcases ht.eq_or_lt with hz | hp
  · simp [←hz]
  rw [Complex.mem_slitPlane_iff] at ha ⊢
  simp only [Complex.add_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.add_im,Complex.one_im,Complex.mul_im,zero_add,add_zero]
  rcases ha with hr | hi
  · exact Or.inl (by positivity)
  · exact Or.inr (mul_ne_zero hp.ne' hi)

private theorem log_ray_derivative (a : ℂ) (ha : a∈Complex.slitPlane) (t : ℝ) (ht : 0≤t) :
    HasDerivAt (fun s : ℝ => Complex.log (1+(s:ℂ)*a)) (a/(1+(t:ℂ)*a)) t := by
  have h := (((hasDerivAt_id (t:ℂ)).mul_const a).const_add 1).clog (ray_slit ha ht)
  simpa [id_eq] using h.comp_ofReal

/-- Integral of a difference of complex resolvents along a positive ray. Each
logarithm is the principal branch and the two real logarithms at infinity cancel. -/
theorem log_ray_integral {a b : ℂ} (ha : a∈Complex.slitPlane) (hb : b∈Complex.slitPlane)
    (hi : IntegrableOn (fun t : ℝ => ((1+(t:ℂ)*a)⁻¹-(1+(t:ℂ)*b)⁻¹)/(t:ℂ)) (Ioi 0)) :
    (∫ t : ℝ in Ioi 0, ((1+(t:ℂ)*a)⁻¹-(1+(t:ℂ)*b)⁻¹)/(t:ℂ)) = Complex.log b-Complex.log a := by
  let F := fun t : ℝ => Complex.log (1+(t:ℂ)*b)-Complex.log (1+(t:ℂ)*a)
  have hc : ContinuousAt F 0 := ((log_ray_derivative b hb 0 le_rfl).sub (log_ray_derivative a ha 0 le_rfl)).continuousAt
  have hd (t : ℝ) (ht : t∈Ioi (0:ℝ)) : HasDerivAt F (((1+(t:ℂ)*a)⁻¹-(1+(t:ℂ)*b)⁻¹)/(t:ℂ)) t := by
    convert (log_ray_derivative b hb t ht.le).sub (log_ray_derivative a ha t ht.le) using 1
    field_simp [Complex.slitPlane_ne_zero (ray_slit ha ht.le),Complex.slitPlane_ne_zero (ray_slit hb ht.le),
        Complex.ofReal_ne_zero.mpr (ne_of_gt ht)] <;> ring
  have hlim (c : ℂ) (hs : c∈Complex.slitPlane) :
      Tendsto (fun t : ℝ => Complex.log (1+(t:ℂ)*c) - (log t:ℂ)) atTop (𝓝 (Complex.log c)) := by
    have h0 : Tendsto (fun t : ℝ => ((t⁻¹:ℝ):ℂ)+c) atTop (𝓝 c) := by
      simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_inv_atTop_zero (𝕜:=ℝ))).add_const c
    apply ((continuousAt_clog hs).tendsto.comp h0).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    change Complex.log (((t⁻¹:ℝ):ℂ)+c) = _
    have he : 1+(t:ℂ)*c=(t:ℂ)*(((t⁻¹:ℝ):ℂ)+c) := by
      rw [Complex.ofReal_inv,mul_add,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne')]
    have hn : ((t⁻¹:ℝ):ℂ)+c≠0 := fun hz => by
      have h := Complex.slitPlane_ne_zero (ray_slit hs ht.le)
      rw [he,hz,mul_zero] at h; exact h rfl
    rw [he,Complex.log_ofReal_mul ht hn]; ring
  have ht : Tendsto F atTop (𝓝 (Complex.log b-Complex.log a)) := by
    simpa [F,sub_sub_sub_cancel_right] using (hlim b hb).sub (hlim a ha)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousWithinAt hd hi ht
  simpa [F] using h

end Liu
