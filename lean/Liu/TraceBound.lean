module

public import Liu.IsolatedEnergy
public import Liu.IsolatedBounds

@[expose] public section

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

def isolatedDensity (m : ℝ) (w : ℂ) (x : ℝ) (z : ℂ) : ℝ :=
  z.im/‖z-(x:ℂ)‖^2 * (m/‖z-w‖^2)

private theorem pole_coordinates (w : ℂ) : (w.re:ℂ)-((-w.im:ℝ):ℂ)*Complex.I = w := by
  apply Complex.ext <;> simp

theorem pole_traceDensity {m : ℝ} (hm : 0 < m) {w z : ℂ} (hw : w.im<0) (hz : z ∈ upper) (x : ℝ) :
    traceDensity (pole m w) x z = Complex.I*(isolatedDensity m w x z:ℂ) := by
  have he : z≠w := fun he => by
    change 0<z.im at hz
    rw [he] at hz; linarith
  rw [traceDensity,singlePole_source hm he]
  dsimp [isolatedDensity]
  push_cast
  ring

theorem isolatedDensity_integral {m : ℝ} (hm : 0 < m) {w : ℂ} (hw : w.im<0) (x : ℝ) :
    Integrable (isolatedDensity m w x) upperArea ∧
    (∫ z, isolatedDensity m w x z ∂upperArea) = m*isolatedTrace w.re (-w.im) x := by
  have hb := neg_pos.mpr hw
  let p := singlePick m w.re (-w.im) hm hb
  have hv : p.value = pole m w := by simpa only [p,pole_coordinates] using singlePick_value m w.re (-w.im) hm hb
  have hi := p.traceDensity_integrable x
  rw [hv] at hi
  have eqn : traceDensity (pole m w) x =ᵐ[upperArea] (fun z => Complex.I*(isolatedDensity m w x z:ℂ)) :=
    (ae_restrict_mem upper_open.measurableSet).mono (fun z hz => pole_traceDensity hm hw hz x)
  have hreal : Integrable (isolatedDensity m w x) upperArea := by
    apply hi.norm.congr
    filter_upwards [eqn,ae_restrict_mem (μ:=area) upper_open.measurableSet] with z he hz
    rw [he,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    apply abs_of_nonneg
    have hz' : 0<z.im := hz
    dsimp [isolatedDensity]; positivity
  refine ⟨hreal,?_⟩
  have hf := field_single_pole w.re x hm hb
  rw [pole_coordinates,←hv,p.field_on_boundary x] at hf
  change Complex.I*(∫ z, traceDensity p.value x z ∂upperArea) = _ at hf
  rw [hv,integral_congr_ae eqn,integral_const_mul,integral_complex_ofReal,←mul_assoc,Complex.I_mul_I] at hf
  exact_mod_cast (show ((∫ z, isolatedDensity m w x z ∂upperArea : ℝ):ℂ) = ((m*isolatedTrace w.re (-w.im) x:ℝ):ℂ) by
    push_cast; linear_combination -hf)

theorem PickSum.field_bounded_by_isolated {n : ℕ} (p : PickSum n) (x : ℝ) :
    ‖field p.value x‖ ≤ ∑ i, p.weight i * isolatedTrace (p.location i).re (-(p.location i).im) x := by
  have hi (i : Fin n) := isolatedDensity_integral (p.pos i) (p.below i) x
  rw [p.field_on_boundary,norm_mul,Complex.norm_I,one_mul]
  change ‖∫ z, traceDensity p.value x z ∂upperArea‖ ≤ _
  simp_rw [←fun i => (hi i).2]
  rw [←integral_finsetSum _ (fun i _ => (hi i).1)]
  apply norm_integral_le_of_norm_le (integrable_finsetSum _ (fun i _ => (hi i).1))
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
  have hz' : 0<z.im := hz
  have hval : p.value z ≠ 0 := fun he => by have hh := p.value_im_pos hz'.le; simp [he] at hh
  have hsource := norm_sum_le (Finset.univ : Finset (Fin n)) (fun i => (p.weight i:ℂ)/(z-p.location i)^2)
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,norm_pow] at hsource
  simp_rw [abs_of_pos (p.pos _)] at hsource
  rw [traceDensity,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),
    source_norm hval,(p.hasDerivAt hz'.le).deriv]
  simp only [isolatedDensity,←Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left hsource (show 0 ≤ z.im/‖z-(x:ℂ)‖^2 by positivity)
  convert h using 1 <;> ring

end Liu
