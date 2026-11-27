module

public import Liu.PrefixEnvelope
public import Liu.DepthDerivative

@[expose] public section

noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
namespace Liu

theorem overlap_small_depth {s γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0<u) (hu₁ : u≤1/4) :
    |k₀*(4*normalMass s*(1-normalMass s)*(sin γ+2*u)/(cos γ^2+(sin γ+2*u)^2))|≤8 := by
  let a := normalMass s
  let b := 1-a
  let t := sin γ+2*u
  have ha : 0<a := Certificate.normalMass_pos _
  have hb : 0<b := by dsimp [b,a]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _
  have hs := sin_nonneg_of_nonneg_of_le_pi hg.1 (hg.2.trans (by linarith [pi_pos]))
  have ht : 0<t := by dsimp [t]; linarith
  have ht₁ : t≤2 := by dsimp [t]; linarith [sin_le_one γ]
  have hd : 1≤cos γ^2+t^2 := by dsimp only [t]; nlinarith [sin_sq_add_cos_sq γ,mul_nonneg hs hu.le,sq_nonneg u]
  have hD : 0<cos γ^2+t^2 := by linarith
  have hab : a*b≤1/4 := by dsimp [b]; nlinarith [sq_nonneg (a-1/2)]
  have hk : 0≤k₀ := by unfold k₀; positivity
  have hk₁ : k₀≤2 := by unfold k₀; nlinarith [pow_le_pow_left₀ pi_pos.le pi_lt_four.le 2]
  change |k₀*(4*a*b*t/(cos γ^2+t^2))|≤8
  rw [abs_of_nonneg (by positivity)]
  have hquot : 4*a*b*t/(cos γ^2+t^2)≤2 := by
    apply (div_le_iff₀ hD).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hab ht.le,ht₁,hd]
  nlinarith only [mul_le_mul_of_nonneg_left hquot hk,hk₁]

/-- Lemma 5.4, the pointwise logarithmic bound uniformly over all angles.
The proof uses only the trace bounds in E.3 and the physical flux
decomposition; the mixed-edge coefficient is unnecessary for this bound. -/
theorem small_depth_flux_estimate : Certificate.smallDepthEstimate := by
  intro s γ u hg hu hu₁
  let a := normalMass s
  let b := 1-a
  let μ := Certificate.smallMass s
  let C := (2:ℝ)^15/μ
  let L := 1+log (1/u)
  let d := sin γ+u
  let A := fun x => a*isolatedTrace 0 u x
  let B := fun x => b*isolatedTrace (cos γ) d x
  let c := edgeRealTrace s γ u
  let q := edgeImagTrace s γ u
  let J := fun x => a*cutTrace 0 u x + b*cutTrace (cos γ) d x
  have ha : 0<a := Certificate.normalMass_pos _
  have hb : 0<b := by dsimp [a,b]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _
  have hμ : 0<μ := lt_min ha hb
  have hμ₁ : μ≤1 := (min_le_right ..).trans (by linarith [Certificate.normalMass_pos s])
  have hC : 0≤C := by dsimp [C]; positivity
  have hab : a+b=1 := by dsimp [b]; ring
  have hL : 1≤L := by dsimp [L]; linarith [log_nonneg ((one_le_div hu).mpr (by linarith : u≤1))]
  have hs := sin_nonneg_of_nonneg_of_le_pi hg.1 (hg.2.trans (by linarith [pi_pos]))
  have hud : u≤d := by dsimp [d]; linarith
  have hd := hu.trans_le hud
  obtain ⟨hci,hcn,hcs,hqm,hqn⟩ := uniform_edge_norms s hg hu.le
  have hqi : Integrable (fun x => q x^2) := (memLp_two_iff_integrable_sq hqm.aestronglyMeasurable).mp hqm
  obtain ⟨hi₁,hv₁⟩ := cutTrace_integral_bound hu le_rfl (by linarith) 0
  obtain ⟨hi₂,hv₂⟩ := cutTrace_integral_bound hu hud (by linarith) (cos γ)
  have hJi : Integrable J := (hi₁.const_mul a).add (hi₂.const_mul b)
  have hJn : (∫ x, J x)/π≤L := by
    unfold J; rw [integral_add (hi₁.const_mul a) (hi₂.const_mul b),integral_const_mul,integral_const_mul]
    change (∫ x, cutTrace 0 u x)/π≤L at hv₁
    change (∫ x, cutTrace (cos γ) d x)/π≤L at hv₂
    rw [add_div,mul_div_assoc,mul_div_assoc]
    nlinarith only [mul_le_mul_of_nonneg_left hv₁ ha.le,mul_le_mul_of_nonneg_left hv₂ hb.le,congrArg (fun v : ℝ => v*L) hab]
  have hP : Integrable (poissonLine 0 1) := Integrable.of_integral_ne_zero ((poissonLine_integral 0 zero_lt_one) ▸ pi_ne_zero)
  let U := fun x => (160+100*C)*J x+100*poissonLine 0 1 x
  let V := fun x => U x+(8+5*C)*|c x|
  let G := fun x => V x+q x^2
  have hUi : Integrable U := (hJi.const_mul _).add (hP.const_mul _)
  have hVi : Integrable V := hUi.add (hci.abs.const_mul _)
  have hGi : Integrable G := hVi.add hqi
  have hpt (x : ℝ) : ‖edgeFluxTerms s γ u x‖≤G x := by
    have hA : 0≤A x := mul_nonneg ha.le (isolatedTrace_nonneg _ _ hu)
    have hB : 0≤B x := mul_nonneg hb.le (isolatedTrace_nonneg _ _ hd)
    have hh := prefix_product_envelope (s:=s) hg hu hC (hcs x) x
    change 2*A x*B x+2*(A x+B x)*|c x|≤ U x+8*|c x| at hh
    have hv : |c x|≤5*C := hcs x
    have hsq := mul_le_mul_of_nonneg_right hv (abs_nonneg (c x))
    have he := edge_components_at_positive_depth (s:=s) hg hu x
    rw [Real.norm_eq_abs,edgeFluxTerms,he.1,he.2]
    change |2*A x*B x+2*(A x+B x)*c x + c x^2 + q x^2|≤U x+(8+5*C)*|c x|+q x^2
    rw [←sq,sq_abs] at hsq
    apply abs_le.mpr
    constructor
    · nlinarith only [hh,hsq,mul_le_mul_of_nonneg_left (neg_le_abs (c x)) (add_nonneg hA hB),
        mul_nonneg hA hB,sq_nonneg (c x),sq_nonneg (q x)]
    · nlinarith only [hh,hsq,mul_le_mul_of_nonneg_left (le_abs_self (c x)) (add_nonneg hA hB)]
  have hnorm := norm_integral_le_of_norm_le hGi (ae_of_all _ hpt)
  change |∫ x, edgeFluxTerms s γ u x|≤∫ x, G x at hnorm
  have hGnorm : (∫ x, G x)/π≤ (160+100*C)*L+100+(8+5*C)*C+C^2 := by
    unfold G; rw [integral_add hVi hqi]
    unfold V; rw [integral_add hUi (hci.abs.const_mul (8+5*C)),integral_const_mul]
    unfold U; rw [integral_add (hJi.const_mul (160+100*C)) (hP.const_mul 100),integral_const_mul,integral_const_mul,
      poissonLine_integral 0 zero_lt_one]
    change (∫ x, |c x|)/π≤C at hcn
    change (∫ x, q x^2)/π≤C^2 at hqn
    simp only [add_div,mul_div_assoc,div_self pi_ne_zero,mul_one]
    linarith only [mul_le_mul_of_nonneg_left hJn (by positivity : 0≤160+100*C),
      mul_le_mul_of_nonneg_left hcn (by positivity : 0≤8+5*C),hqn]
  have hfit : (160+100*C)+100+(8+5*C)*C+C^2+8≤2^34/μ^2 := by
    unfold C
    field_simp [hμ.ne']
    nlinarith only [hμ₁,pow_le_pow_left₀ hμ.le hμ₁ 2]
  obtain ⟨_,hflux⟩ := edge_flux_decomposition (s:=s) hg hu
  rw [hflux]
  apply (abs_sub _ _).trans
  rw [abs_div,abs_of_pos pi_pos]
  apply (add_le_add ((div_le_div_of_nonneg_right hnorm pi_pos.le).trans hGnorm) (overlap_small_depth hg hu hu₁)).trans
  change (160+100*C)*L+100+(8+5*C)*C+C^2+8≤2^34/μ^2*L
  apply le_trans _ (mul_le_mul_of_nonneg_right hfit (by linarith : 0≤L))
  nlinarith only [mul_le_mul_of_nonneg_left hL (show 0≤100+(8+5*C)*C+C^2+8 by positivity)]

theorem pair_deficit_of_two_inputs (p : Pair) (box : Certificate.boxBounds)
    (mixed : Certificate.mixedEdgeEstimate) : k₀*p.mass^2<deficit p.value :=
  pair_deficit_of_three_inputs p box small_depth_flux_estimate mixed

theorem two_pole_test_of_two_inputs (p : Pair) (box : Certificate.boxBounds)
    (mixed : Certificate.mixedEdgeEstimate) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2<deficit p.value ∧ p.slope<0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0<ε → ε<ε₀ → p.quotientDomain ε ∧ quotient (critical p ε)<k₀ :=
  two_pole_test_of_three_inputs p box small_depth_flux_estimate mixed

end Liu
