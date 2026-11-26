import Liu.DirichletLocalEstimate

noncomputable section
open Set Filter MeasureTheory Real Complex Metric InnerProductSpace
open scoped ContDiff Topology ComplexConjugate
namespace Liu

private theorem lap_conjugate {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper) {w : ℂ} (hw : w∈upper) :
    dirLap (fun z => conj (V z)) w=conj (dirLap V w) := by
  have hc := Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn h
  erw [dirLap_inside hc hw,dirLap_inside h hw]
  exact congrFun (laplacian_CLE_comp_left (l:=Complex.conjCLE) (f:=V)) w

private theorem gradient_of_fields {V : ℂ → ℂ} (hV : ContDiffOn ℝ ∞ V closedUpper)
    {z : ℂ} (hz : z∈closedUpper) {T : ℝ} (h₁ : ‖dirField V z‖≤T)
    (h₂ : ‖dirField (fun w => conj (V w)) z‖≤T) :
    ‖fderivWithin ℝ V closedUpper z‖≤T := by
  let D := fderivWithin ℝ V closedUpper z
  let W := dirField V z
  let U := conj (dirField (fun w => conj (V w)) z)
  have hU : ‖U‖≤T := (Complex.norm_conj _).le.trans h₂
  have Ueq : U= -(D 1+I*D I) := by
    dsimp only [U,dirField]; rw [dirPart_conj hV hz,dirPart_conj hV hz]
    simp only [map_neg,map_sub,map_mul,Complex.conj_conj,Complex.conj_I,neg_mul,sub_neg_eq_add]; rfl
  have Weq : W= -(D 1-I*D I) := rfl
  have decomp (v : ℂ) : (2:ℂ)*D v= -(v*W+conj v*U) := by
    rw [Weq,Ueq]
    have hv : v.re • (1:ℂ)+v.im • I=v := by simpa only [Complex.real_smul,mul_one] using Complex.re_add_im v
    have hα := congrArg D hv
    rw [map_add,D.map_smul,D.map_smul] at hα
    simp only [Complex.real_smul] at hα
    rw [←hα]
    have hc := congrArg conj (Complex.re_add_im v)
    simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg] at hc
    linear_combination (norm := (ring_nf <;> simp [Complex.I_sq] <;> ring)) (D 1-I*D I) * (Complex.re_add_im v) + (D 1+I*D I)*hc
  apply ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans h₁)
  intro v
  have hb := (norm_add_le (v*W) (conj v*U)).trans (add_le_add
    ((norm_mul v W).le.trans (mul_le_mul_of_nonneg_left h₁ (norm_nonneg v)))
    ((norm_mul (conj v) U).le.trans (mul_le_mul_of_nonneg_left hU (norm_nonneg _))))
  rw [←norm_neg,←decomp,norm_mul,Complex.norm_ofNat,Complex.norm_conj] at hb
  change ‖D v‖≤T*‖v‖
  linarith

/-- The ball form of the boundary and interior gradient bound for arbitrary
complex-valued smooth zero-Dirichlet data, including boundary observations. -/
theorem dirichlet_gradient_ball :
    ∃ C≥0, ∀ {V : ℂ → ℂ}, ContDiffOn ℝ ∞ V closedUpper → (∀ x : ℝ, V x=0) →
    ∀ {z : ℂ}, z∈closedUpper → ∀ {R A B : ℝ}, 0<R → 0≤A → 0≤B →
    (∀ w∈upper, ‖z-w‖<R → ‖V w‖≤A) →
    (∀ w∈upper, ‖z-w‖<R → ‖Laplacian.laplacian V w‖≤B) →
    ‖fderivWithin ℝ V closedUpper z‖≤C*(A/R+R*B) := by
  obtain ⟨C,hC,H⟩ := dirField_ball_estimate
  refine ⟨C,hC,?_⟩
  intro V hV hb z hz R A B hR hA hB ha hl
  have hL (w : ℂ) (hw : w∈upper) (hr : ‖z-w‖<R) : ‖dirLap V w‖≤B := by rw [dirLap_inside hV hw]; exact hl w hw hr
  apply gradient_of_fields hV hz (H hV hb hz hR hA hB ha hL)
  exact H (Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hV) (fun x => by simp [hb])
    hz hR hA hB (fun w hw hr => (Complex.norm_conj _).le.trans (ha w hw hr))
    (fun w hw hr => by erw [lap_conjugate hV hw,Complex.norm_conj]; exact hL w hw hr)

private theorem cubic_dirField_bound {B : ℝ} (hB : 0≤B) :
    ∃ C≥0, ∀ {V : ℂ → ℂ}, ContDiffOn ℝ ∞ V closedUpper → (∀ x : ℝ, V x=0) →
    (∃ A≥0, ∀ w∈upper, ‖V w‖≤A) → (∀ w∈upper, ‖dirLap V w‖≤B/(1+‖w‖)^3) →
    ∀ z∈closedUpper, 1<‖z‖ → ‖dirField V z‖≤C*(1+Real.log ‖z‖)/‖z‖^2 := by
  obtain ⟨C,hC,H⟩ := canonicalField_uniform_cubic_error hB
  refine ⟨C,hC,?_⟩
  intro V hV hb hbnd hL z hz hr
  obtain ⟨A,hA,ha⟩ := hbnd
  let f := upper.indicator (dirLap V)
  have hin : upper⊆closedUpper := fun w hw => (show 0<w.im from hw).le
  classical
  have hm : Measurable f := ((dirLap_smooth hV).continuousOn.mono hin).measurable_piecewise
    (continuousOn_const (c:=(0:ℂ))) upper_open.measurableSet
  have hsrc (w : ℂ) (hw : w∈upper) : ‖f w‖≤B/(1+‖w‖)^3 := by rw [show f w=dirLap V w from indicator_of_mem hw _]; exact hL w hw
  have g := GreenSource.of_decay (by norm_num : (2:ℝ)<3) hB hm (by simpa only [Real.rpow_ofNat] using hsrc)
  have fe : f=ᵐ[upperArea] dirLap V := by filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw using indicator_of_mem hw _
  obtain ⟨K,hK,hq⟩ := g.decay
  have hi := (resolvent_source_integrable hm hK hq hz).1
  have eq : (fun w => greenResolvent z w*f w)=ᵐ[upperArea] (fun w => greenResolvent z w*dirLap V w) :=
    fe.mono (fun w hw => congrArg (fun q => greenResolvent z w*q) hw)
  rw [bounded_dirField_representation hV hb hA ha (g.integrable.congr fe) hz (hi.congr eq),←integral_congr_ae eq,norm_mul]
  have hh := H f hm hsrc z hz hr
  rw [canonicalField_eq_integral g.quadratic,norm_neg] at hh
  exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num : ‖(1/2:ℂ)‖≤1)).trans hh

theorem dirichlet_gradient_cubic {B : ℝ} (hB : 0≤B) :
    ∃ C≥0, ∀ {V : ℂ → ℂ}, ContDiffOn ℝ ∞ V closedUpper → (∀ x : ℝ, V x=0) →
    (∃ A≥0, ∀ w∈upper, ‖V w‖≤A) → (∀ w∈upper, ‖Laplacian.laplacian V w‖≤B/(1+‖w‖)^3) →
    ∀ z∈closedUpper, 1<‖z‖ → ‖fderivWithin ℝ V closedUpper z‖≤C*(1+Real.log ‖z‖)/‖z‖^2 := by
  obtain ⟨C,hC,H⟩ := cubic_dirField_bound hB
  refine ⟨C,hC,?_⟩
  intro V hV hb hbnd hL z hz hr
  have hl (w : ℂ) (hw : w∈upper) : ‖dirLap V w‖≤B/(1+‖w‖)^3 := by rw [dirLap_inside hV hw]; exact hL w hw
  apply gradient_of_fields hV hz (H hV hb hbnd hl z hz hr)
  obtain ⟨A,hA,ha⟩ := hbnd
  exact H (Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hV) (fun x => by simp [hb])
    ⟨A,hA,fun w hw => (Complex.norm_conj _).le.trans (ha w hw)⟩
    (fun w hw => by erw [lap_conjugate hV hw,Complex.norm_conj]; exact hl w hw) z hz hr

end Liu
