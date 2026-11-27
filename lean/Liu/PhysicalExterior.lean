module

public import Liu.CutoffIdentification
public import Liu.WitnessClaim

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter Metric
open scoped ComplexConjugate Topology
namespace Liu

/-- Extend the difference of the two physical forcings by zero across the boundary. -/
def PickSum.exteriorError {n : ℕ} (p : PickSum n) (t : ℝ) : ℂ → ℂ :=
  upper.indicator (fun z => p.frozenLogSource t z-cutoffSource p.mass t z)

private theorem error_regular {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    Measurable (p.exteriorError t) ∧ DifferentiableOn ℝ (p.exteriorError t) upper := by
  classical
  have d := (p.log_sources_differentiable t).2.sub (cutoffSource_differentiable p.mass ht ht1)
  have he : EqOn (p.exteriorError t) (p.frozenLogSource t-cutoffSource p.mass t) upper := fun z hz => indicator_of_mem hz _
  exact ⟨d.continuousOn.measurable_piecewise (continuous_const.continuousOn : ContinuousOn (fun _ : ℂ => (0:ℂ)) upperᶜ) upper_open.measurableSet,d.congr he⟩

theorem PickSum.exteriorError_uniform {n : ℕ} (p : PickSum n) :
    ∃ K ≥ 0, ∀ t : ℝ, 0<t → t<1 → t*π≤1/2 → ∀ w∈upper, ‖p.exteriorError t w‖ ≤ K/(1+‖w‖)^3 := by
  obtain ⟨A,hA,T,hT,hfar⟩ := p.exterior_frozen_source_error
  let R := max 3 T
  have hR : 1≤R := (by norm_num : (1:ℝ)≤3).trans (le_max_left ..)
  obtain ⟨B,hB,hcore⟩ := cutoff_uniform_core_bounds p.mass_pos hR
  obtain ⟨D,hD,hρ⟩ := p.frozen_source_quadratic_bound
  refine ⟨(D+B)*(1+R)^3+8*A,by positivity,?_⟩
  intro t ht ht1 hs w hw
  have hy : 0≤w.im := le_of_lt hw
  rw [PickSum.exteriorError,indicator_of_mem hw]
  apply (le_div_iff₀ (by positivity : 0<(1+‖w‖)^3)).mpr
  by_cases hr : ‖w‖≤R
  · have hb := (hcore t ht ht1 hs w hy hr).2.2
    have hd := (hρ t ⟨ht.le,ht1.le⟩ w hw).trans (div_le_self hD (one_le_pow₀ (by linarith [norm_nonneg w] : 1≤1+‖w‖)))
    apply (mul_le_mul ((norm_sub_le ..).trans (add_le_add hd hb)) (pow_le_pow_left₀ (by positivity) (by linarith : 1+‖w‖≤1+R) 3) (by positivity) (by positivity)).trans
    exact le_add_of_nonneg_right (by positivity)
  · have h3 := (le_max_left ..).trans_lt (lt_of_not_ge hr)
    have hp : 0<‖w‖ := by linarith
    rw [cutoffSource_far p.mass_pos hy (by linarith)]
    have hf := hfar t ⟨ht.le,ht1.le⟩ w hy ((le_max_right ..).trans (le_of_not_ge hr))
    apply (mul_le_mul hf (pow_le_pow_left₀ (by positivity) (by linarith : 1+‖w‖≤2*‖w‖) 3) (by positivity) (by positivity)).trans
    have he : A/‖w‖^3*(2*‖w‖)^3=8*A := by field_simp [hp.ne']; ring
    exact he.le.trans (le_add_of_nonneg_left (by positivity))

private theorem uniform_error_supercritical {f : ℂ → ℂ} (hm : Measurable f) {K : ℝ} (hK : 0≤K)
    (hb : ∀ w ∈ upper, ‖f w‖≤K/(1+‖w‖)^3) : SupercriticalSource f (1/2) := by
  refine ⟨by norm_num,by norm_num,hm,K,hK,?_⟩
  intro w hw
  apply (hb w hw).trans (div_le_div_of_nonneg_left hK (by positivity) ?_)
  simpa only [rpow_ofNat] using rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg w] : 1≤1+‖w‖)
    (by norm_num : 2+1/2≤(3:ℝ))

theorem PickSum.frozen_cutoff_difference {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0<t) (ht1 : t<1) (hs : t*π≤1/2) :
    EqOn (canonicalField (p.frozenLogSource t)-cutoffField p.mass t) (canonicalField (p.exteriorError t)) upper := by
  obtain ⟨K,hK,hb⟩ := p.exteriorError_uniform
  obtain ⟨hm,hd⟩ := error_regular p ht ht1
  have herr := uniform_error_supercritical hm hK (hb t ht ht1 hs)
  have hρ := (p.supercritical_sources ht ht1).2
  have dρ := (p.log_sources_differentiable t).2
  obtain ⟨hL,hZ⟩ := cutoffField_projection p.mass_pos ht ht1 hs
  have dF (z : ℂ) (hz : z∈upper) := canonicalField_dbar hρ.green.quadratic hz (dρ.differentiableAt (upper_open.mem_nhds hz))
  have dV (z : ℂ) (hz : z∈upper) := cutoffField_equation p.mass ht ht1 (le_of_lt hz) (show z≠0 from fun he => by simpa [he,upper] using hz)
  have hF := hρ.field_memLp
  have hdiff := hF.sub hL
  apply herr.identify_field hd hdiff (fun z hz => ((dF z hz).1.sub (dV z hz).1).differentiableWithinAt)
  · intro z hz
    rw [PickSum.exteriorError,indicator_of_mem hz,←(dF z hz).2,←(dV z hz).2]
    unfold dbar
    rw [((dF z hz).1.hasFDerivAt.sub (dV z hz).1.hasFDerivAt).fderiv]
    simp only [sub_apply]; ring
  · have hP := hρ.projection_zero
    simp only [asL2,dif_pos hF] at hP
    simp only [asL2,dif_pos hL] at hZ
    simp only [asL2,dif_pos hdiff,MemLp.toLp_sub hF hL,map_sub,hP,hZ,sub_zero]

/-- Uniform comparison of the frozen field and the actual derivative of the
exterior Dirichlet model. It holds all the way down to either real edge by continuity. -/
theorem PickSum.frozen_exterior_field_error {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ t : ℝ, 0<t → t<1 → t*π≤1/2 → ∀ z : ℂ, 0≤z.im → 2<‖z‖ →
      ‖canonicalField (p.frozenLogSource t) z-exteriorField p.mass t z‖ ≤ C*(1+log ‖z‖)/‖z‖^2 := by
  obtain ⟨K,hK,hb⟩ := p.exteriorError_uniform
  obtain ⟨C,hC,h⟩ := canonicalField_uniform_cubic_error hK
  refine ⟨C,hC,?_⟩
  intro t ht ht1 hs z hz hr
  obtain ⟨hm,hd⟩ := error_regular p ht ht1
  have hρ := (p.supercritical_sources ht ht1).2
  have herr := uniform_error_supercritical hm hK (hb t ht ht1 hs)
  have he := p.frozen_cutoff_difference ht ht1 hs
  let U := {w : ℂ | 0≤w.im}
  have hc : ContinuousOn (canonicalField (p.frozenLogSource t)-cutoffField p.mass t) U :=
    (canonicalField_continuous hρ.green.quadratic).continuousOn.sub (cutoff_continuous_closed p.mass ht ht1).2
  have hclosed : IsClosed U := isClosed_le continuous_const Complex.continuous_im
  have hc' := hclosed.isClosed_eq hc (canonicalField_continuous herr.green.quadratic).continuousOn
  have hsub : upper ⊆ {w ∈ U | (canonicalField (p.frozenLogSource t)-cutoffField p.mass t) w=canonicalField (p.exteriorError t) w} :=
    fun w hw => ⟨(show 0<w.im from hw).le,he hw⟩
  have he' := closure_minimal hsub hc'
  rw [closure_upper_plane] at he'
  rw [←cutoffField_far p.mass t hz hr]
  change ‖(canonicalField (p.frozenLogSource t)-cutoffField p.mass t) z‖≤_
  rw [(he' hz).2]; exact h _ hm (hb t ht ht1 hs) z hz (by linarith)

end Liu
