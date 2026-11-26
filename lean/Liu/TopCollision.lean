import Liu.CoalescentFlux
import Liu.TopInterpolationChart

noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
namespace Liu

private theorem pole_flux_zero_at {p : ℂ} (hp : p.im<0) : boundaryFlux (pole 1 p)=0 := by
  have he : (p.re:ℂ)-((-p.im:ℝ):ℂ)*Complex.I=p := by apply Complex.ext <;> simp
  rw [←he]
  exact single_pole_flux_zero p.re (m:=1) zero_lt_one (neg_pos.mpr hp)

/-- A coincident two-pole family following a common physical trajectory has
zero flux for every real parameter in its separated neighborhood. -/
private theorem coincident_real_flux {a : ℝ} (ha : 0<a) (h₁ : a<1) (p v : ℂ) {r : ℝ}
    (hr : (r:ℂ)∈(PickChart.moving a p v v).domain univ) :
    (PickChart.moving a p v v).fluxExtension r = 0 := by
  let P := PickChart.moving (a:ℂ) p v v
  have h := PickChart.moving_regular (a:ℂ) p v v
  have he : P.realSum r a = pole 1 (p+(r:ℂ)*v) := by
    funext z; simp [PickChart.realSum,P,PickChart.moving,pole,div_eq_mul_inv]; ring
  rw [h.flux_agrees hr (show P.mass r=(a:ℂ) from rfl) ha h₁,he,
    pole_flux_zero_at (p:=p+(r:ℂ)*v) (h.left_below r hr),Complex.ofReal_zero]

theorem coalescent_flux_deriv_zero {a : ℝ} (ha : 0<a) (h₁ : a<1) {p : ℂ} (hp : p.im<0)
    (l r : ℂ) : deriv (PickChart.moving a p l r).fluxExtension 0 = 0 := by
  let v := PickChart.velocity (a:ℂ) l r
  let Q := PickChart.moving (a:ℂ) p v v
  have hQ := PickChart.moving_regular (a:ℂ) p v v
  have hO : (0:ℂ)∈Q.domain univ := PickChart.moving_origin hp
  obtain ⟨_,d,hP',hQ'⟩ := PickChart.moving_flux_first_order (a:=(a:ℂ)) (l:=l) (r:=r) hp
  change HasDerivAt Q.fluxExtension d 0 at hQ'
  have hd : HasDerivAt (fun t : ℝ => Q.fluxExtension t) d 0 :=
    (show HasDerivAt Q.fluxExtension d ((0:ℝ):ℂ) by simpa using hQ').comp_ofReal
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, (t:ℂ)∈Q.domain univ :=
    Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (by simpa using hQ.isOpen.mem_nhds hO)
  have hzero : (fun _ : ℝ => (0:ℂ)) =ᶠ[𝓝 0] (fun t : ℝ => Q.fluxExtension t) :=
    hnear.mono fun t ht => (coincident_real_flux ha h₁ p v ht).symm
  exact hP'.deriv.trans ((hd.congr_of_eventuallyEq hzero).unique (hasDerivAt_const 0 0))

/-- The continuous reciprocal-depth value at zero is zero for every real
log mass and angle. The normalized flux thus has a constant horizontal
extension when the fixed depth is the top focus. -/
theorem top_focus_limit (s γ : ℝ) :
    Tendsto (fun v : ℝ => v⁻¹ * boundaryFlux (unitDepthSum s γ v)) (𝓝 0) (𝓝 0) := by
  let a := normalMass s
  let P := PickChart.moving (a:ℂ) (-Complex.I) 0 (direction γ)
  have ha : 0<a := Certificate.normalMass_pos s
  have h₁ : a<1 := by dsimp [a]; linarith [Certificate.complement_normalMass s,Certificate.normalMass_pos (-s)]
  have h := PickChart.moving_regular (a:ℂ) (-Complex.I) 0 (direction γ)
  have hc : (0:ℂ)∈P.domain univ := PickChart.moving_origin (by simp)
  have hr : ∀ᶠ v : ℝ in 𝓝 0, (v:ℂ)∈P.domain univ :=
    Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (by simpa using h.isOpen.mem_nhds hc)
  have agree {v : ℝ} (hv : (v:ℂ)∈P.domain univ) : P.fluxExtension v=(boundaryFlux (unitDepthSum s γ v):ℂ) := by
    have he : P.realSum v a = unitDepthSum s γ v := by
      funext z; simp [PickChart.realSum,P,PickChart.moving,unitDepthSum,a]
    rw [h.flux_agrees hv (show P.mass v=(a:ℂ) from rfl) ha h₁,he]
  have h0 : P.fluxExtension 0=0 := by simpa [unitDepth_flux_zero] using agree (v:=0) (by simpa using hc)
  have hdz : deriv P.fluxExtension 0=0 := coalescent_flux_deriv_zero ha h₁ (by simp) _ _
  have hds := ((Complex.differentiableOn_dslope (h.isOpen.mem_nhds hc)).mpr
    h.flux_analytic.differentiableOn).continuousOn.continuousAt (h.isOpen.mem_nhds hc)
  have hev : (fun v : ℝ => (dslope P.fluxExtension 0 (v:ℂ)).re) =ᶠ[𝓝 0]
      fun v => v⁻¹*boundaryFlux (unitDepthSum s γ v) := by
    filter_upwards [hr] with v hv
    by_cases hne : v=0
    · simp [hne,hdz]
    · rw [dslope_of_ne _ (Complex.ofReal_ne_zero.mpr hne),slope_def_module,h0,sub_zero,sub_zero,smul_eq_mul,agree hv]
      norm_cast
  have hds' : Tendsto (dslope P.fluxExtension 0) (𝓝 (0:ℂ)) (𝓝 0) := by
    have hh : Tendsto (dslope P.fluxExtension 0) (𝓝 0) (𝓝 (dslope P.fluxExtension 0 0)) := hds.tendsto
    simpa only [dslope_same,hdz] using hh
  have hreal : Tendsto (fun v : ℝ => (v:ℂ)) (𝓝 0) (𝓝 (0:ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto
  have hre : Tendsto Complex.re (𝓝 (0:ℂ)) (𝓝 0) := Complex.continuous_re.continuousAt.tendsto
  exact (hre.comp (hds'.comp hreal)).congr' hev

end Liu
