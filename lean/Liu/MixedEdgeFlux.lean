module

public import Liu.MixedNorm
public import Liu.MixedPairBound

@[expose] public section

noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology
namespace Liu

private theorem mixed_cut_log {u : ℝ} (hu : 0<u) (hu₁ : u≤1/4) :
    |(∫ x, cutTrace 0 u x)/π-log (1/u)|≤1 := by
  have h := isolatedTrace_log_moment 0 hu
  have ht : 1+u⁻¹=(1/u)*(1+u) := by field_simp [hu.ne']; ring
  have hl := log_le_sub_one_of_pos (by positivity : 0<1+u)
  have hl₀ := log_nonneg (show 1≤1+u by linarith)
  change log (1+u⁻¹)-1≤(∫ x, cutTrace 0 u x)/π ∧ (∫ x, cutTrace 0 u x)/π≤log (1+u⁻¹) at h
  rw [ht,log_mul (by positivity) (by positivity)] at h
  exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩

/-- The mixed-edge logarithmic coefficient is chosen once per physical
mass and angle. The bound is uniform over all printed depths. -/
theorem mixed_edge_flux_estimate : Certificate.mixedEdgeEstimate := by
  intro s γ hg hσ
  let a := normalMass s
  let b := 1-a
  let C := 8/(a*sin γ^4)
  let star := mixedTrace s γ 0 0
  let coeff := mixedLogCoefficient s γ
  have ha : 0<a := Certificate.normalMass_pos _
  have hb : 0<b := by dsimp [a,b]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _
  have ha₁ : a≤1 := by dsimp [b] at hb; linarith
  obtain ⟨hC₈,hsup,_,_,hcoeff⟩ := mixed_trace_controls (s:=s) hg hσ
  change 8≤C at hC₈
  have hC : 0<C := by linarith
  refine ⟨coeff,hcoeff,?_⟩
  intro u hu hu₁
  let L := 1+log (1/u)
  let c := edgeRealTrace s γ u
  let q := edgeImagTrace s γ u
  let H := mixedTrace s γ u
  let B := fun x => b*isolatedTrace (cos γ) (sin γ+u) x
  have hu₀ : u≤1 := by linarith
  have hL : 0≤L := by dsimp [L]; linarith [log_nonneg ((one_le_div hu).mpr hu₀)]
  have hLs : u*L^2≤4 := edge_log_square_bound hu hu₀
  obtain ⟨⟨hBi,hBn⟩,⟨hci,hcn⟩,⟨hqi,hqn⟩,⟨hHi,hHn⟩⟩ := mixed_regular_norms (s:=s) hg hσ hu
  change (∫ x, H x^2)/π≤8*C^2 at hHn
  change (∫ x, B x^2)/π≤C^2 at hBn
  change (∫ x, c x^2)/π≤3*C^2 at hcn
  change (∫ x, q x^2)/π≤4*C^2 at hqn
  have hP : Integrable (poissonLine 0 1) := Integrable.of_integral_ne_zero ((poissonLine_integral 0 zero_lt_one) ▸ pi_ne_zero)
  obtain ⟨hJi,hJn⟩ := cutTrace_integral_bound hu le_rfl hu₀ 0
  change (∫ x, cutTrace 0 u x)/π≤L at hJn
  obtain ⟨hWi,hWv⟩ := edgeLogWeight_mass
  have hWn : (∫ x, edgeLogWeight x)/π≤2 := by rw [hWv,div_le_iff₀ pi_pos]; linarith [pi_gt_three]
  let U := fun x => 132*C*poissonLine 0 1 x + H x^2/C
  let V := fun x => U x + (20*C*u*L)*cutTrace 0 u x
  let T := fun x => V x + 40*C*edgeLogWeight x
  let G₁ := fun x => T x+B x^2
  let G₂ := fun x => G₁ x+2*c x^2
  let G := fun x => G₂ x+q x^2
  have hUi : Integrable U := (hP.const_mul _).add (hHi.div_const C)
  have hVi : Integrable V := hUi.add (hJi.const_mul _)
  have hTi : Integrable T := hVi.add (hWi.const_mul _)
  have hGi₁ : Integrable G₁ := hTi.add hBi
  have hGi₂ : Integrable G₂ := hGi₁.add (hci.const_mul 2)
  have hGi : Integrable G := hGi₂.add hqi
  have hTn : (∫ x, T x)/π≤300*C := by
    unfold T; rw [integral_add hVi (hWi.const_mul (40*C)),integral_const_mul]
    unfold V; rw [integral_add hUi (hJi.const_mul (20*C*u*L)),integral_const_mul]
    unfold U; rw [integral_add (hP.const_mul (132*C)) (hHi.div_const C),integral_const_mul,integral_div,poissonLine_integral 0 zero_lt_one]
    simp only [add_div,mul_div_assoc,div_self pi_ne_zero,mul_one]
    rw [div_right_comm _ C π]
    have hpart : ((∫ x, H x^2)/π)/C≤8*C := (div_le_iff₀ hC).mpr (by nlinarith only [hHn])
    nlinarith only [hpart,mul_le_mul_of_nonneg_left hJn (by positivity : 0≤20*C*u*L),
      mul_le_mul_of_nonneg_left hLs hC.le,mul_le_mul_of_nonneg_left hWn hC.le]
  have hGn : (∫ x, G x)/π≤300*C+11*C^2 := by
    unfold G; rw [integral_add hGi₂ hqi]
    unfold G₂; rw [integral_add hGi₁ (hci.const_mul 2),integral_const_mul]
    unfold G₁; rw [integral_add hTi hBi]
    simp only [add_div,mul_div_assoc]
    linarith only [hTn,hBn,hcn,hqn]
  let R := fun x => edgeFluxTerms s γ u x-coeff*cutTrace 0 u x
  have hpt : ∀ᵐ x : ℝ, ‖R x‖≤G x := by
    filter_upwards [(volume:Measure ℝ).ae_ne (0:ℝ)] with x hx
    let I := isolatedTrace 0 u x
    let P := poissonLine 0 1 x
    let D := 2*a*I*(H x-star*P)
    have hd : |D|≤T x := mixed_pair_majorant hg hσ hu hu₁ hx
    have he : R x=D+2*B x*c x+c x^2+q x^2 := by
      obtain ⟨hr,hi⟩ := edge_components_at_positive_depth (s:=s) hg hu x
      dsimp only [R,edgeFluxTerms]
      rw [hr,hi]
      change 2*(a*I)*(B x)+2*(a*I+B x)*c x+c x^2+q x^2-(2*a*star)*(P*I)=_
      dsimp only [D]
      change _=2*a*I*((B x+c x)-star*P)+2*B x*c x+c x^2+q x^2
      ring
    rw [Real.norm_eq_abs,he]
    change _≤T x+B x^2+2*c x^2+q x^2
    have h := abs_le.mp hd
    exact abs_le.mpr ⟨by nlinarith only [h.1,sq_nonneg (B x+c x),sq_nonneg (c x),sq_nonneg (q x)],
      by nlinarith only [h.2,sq_nonneg (B x-c x)]⟩
  have hR := norm_integral_le_of_norm_le hGi hpt
  have hn : |(∫ x, R x)/π|≤300*C+11*C^2 := by
    rw [abs_div,abs_of_pos pi_pos,←Real.norm_eq_abs]
    exact (div_le_div_of_nonneg_right hR pi_pos.le).trans hGn
  have hstar : |star|≤4*C := hsup 0 le_rfl 0
  have hcf : |coeff|≤8*C := by
    change |2*a*star|≤8*C
    rw [abs_mul,abs_of_pos (by positivity : 0<2*a)]
    nlinarith only [mul_le_mul (show 2*a≤2 by linarith) hstar (abs_nonneg star) (by norm_num : (0:ℝ)≤2)]
  have hmoment : |coeff*((∫ x, cutTrace 0 u x)/π-log (1/u))|≤8*C := by
    rw [abs_mul]; simpa using mul_le_mul hcf (mixed_cut_log hu hu₁) (abs_nonneg _) (by positivity : 0≤8*C)
  obtain ⟨hFi,hflux⟩ := edge_flux_decomposition (s:=s) hg hu
  let O := k₀*(4*a*b*(sin γ+2*u)/(cos γ^2+(sin γ+2*u)^2))
  have hO : |O|≤8 := overlap_small_depth hg hu hu₁
  have he : flux s γ u-coeff*log (1/u)=(∫ x, R x)/π+coeff*((∫ x, cutTrace 0 u x)/π-log (1/u))-O := by
    rw [hflux]
    unfold R; rw [integral_sub hFi (hJi.const_mul coeff),integral_const_mul]
    dsimp only [O,a,b]; ring
  rw [he]
  apply (abs_sub _ _).trans ((add_le_add ((abs_add_le ..).trans (add_le_add hn hmoment)) hO).trans ?_)
  change 300*C+11*C^2+8*C+8≤4096/(a^2*sin γ^8)
  have hfit : 300*C+11*C^2+8*C+8≤64*C^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hC₈ hC.le,hC₈]
  apply hfit.trans_eq
  dsimp [C]; ring

end Liu
