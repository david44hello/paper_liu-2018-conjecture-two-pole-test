import Liu.DirichletGradient

noncomputable section
open Set Metric Filter Real Complex MeasureTheory
open scoped Topology ContDiff InnerProductSpace
namespace Liu

def dirichletAnnulus (r : ℝ) := {w∈upper | r/4<‖w‖ ∧ ‖w‖<2*r}

private theorem annulus_sup_bounds {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper) {r : ℝ} (hr : 0<r) :
    let A := sSup ((fun w => ‖V w‖) '' dirichletAnnulus r)
    let B := sSup ((fun w => ‖Laplacian.laplacian V w‖) '' dirichletAnnulus r)
    0≤A ∧ 0≤B ∧ ∀ w∈dirichletAnnulus r, ‖V w‖≤A ∧ ‖Laplacian.laplacian V w‖≤B := by
  let S := closedBall (0:ℂ) (2*r) ∩ closedUpper
  have hc : IsCompact S := (isCompact_closedBall ..).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hsub : dirichletAnnulus r⊆S := fun w hw => ⟨by simpa using hw.2.2.le,(show 0<w.im from hw.1).le⟩
  obtain ⟨A,ha⟩ := hc.exists_bound_of_continuousOn (h.continuousOn.mono (show S⊆closedUpper from inter_subset_right))
  obtain ⟨B,hb⟩ := hc.exists_bound_of_continuousOn ((dirLap_smooth h).continuousOn.mono (show S⊆closedUpper from inter_subset_right))
  have b₁ : BddAbove ((fun w => ‖V w‖) '' dirichletAnnulus r) := ⟨A,by rintro _ ⟨w,hw,rfl⟩; exact ha w (hsub hw)⟩
  have b₂ : BddAbove ((fun w => ‖Laplacian.laplacian V w‖) '' dirichletAnnulus r) := ⟨B,by
    rintro _ ⟨w,hw,rfl⟩; change ‖Laplacian.laplacian V w‖≤B; rw [←dirLap_inside h hw.1]; exact hb w (hsub hw)⟩
  have non : ∃ w, w∈dirichletAnnulus r := by
    refine ⟨(r:ℂ)*I,?_⟩
    have hn : ‖(r:ℂ)*I‖=r := by rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_of_nonneg hr.le]
    exact ⟨by simpa [upper] using hr,by rw [hn]; linarith,by rw [hn]; linarith⟩
  obtain ⟨w,hw⟩ := non
  have bound (w : ℂ) (hw : w∈dirichletAnnulus r) := And.intro (le_csSup b₁ (mem_image_of_mem _ hw)) (le_csSup b₂ (mem_image_of_mem _ hw))
  exact ⟨(norm_nonneg _).trans (bound w hw).1,(norm_nonneg _).trans (bound w hw).2,bound⟩

/-- Lemma 2.2(a), with the two printed suprema over the open half-annulus
and the one-sided real differential at boundary observations. -/
theorem dirichlet_annular_gradient :
    ∃ C>0, ∀ V : ℂ → ℂ, ContDiffOn ℝ ∞ V closedUpper → (∀ x : ℝ, V x=0) →
    ∀ z∈closedUpper, 0<‖z‖ →
      ‖fderivWithin ℝ V closedUpper z‖ ≤ C*(‖z‖⁻¹*sSup ((fun w => ‖V w‖) '' dirichletAnnulus ‖z‖)+
        ‖z‖*sSup ((fun w => ‖Laplacian.laplacian V w‖) '' dirichletAnnulus ‖z‖)) := by
  obtain ⟨C,hC,H⟩ := dirichlet_gradient_ball
  refine ⟨2*C+1,by linarith,?_⟩
  intro V hV hb z hz hpos
  let r := ‖z‖
  let A := sSup ((fun w => ‖V w‖) '' dirichletAnnulus r)
  let B := sSup ((fun w => ‖Laplacian.laplacian V w‖) '' dirichletAnnulus r)
  obtain ⟨ha,hb',hs⟩ := annulus_sup_bounds hV hpos
  have near (w : ℂ) (hw : w∈upper) (hd : ‖z-w‖<r/2) : w∈dirichletAnnulus r := by
    have ht := norm_add_le (z-w) w
    rw [sub_add_cancel] at ht
    have ht' := norm_add_le (w-z) z
    rw [sub_add_cancel,norm_sub_rev w z] at ht'
    exact ⟨hw,by dsimp [r] at *; linarith,by dsimp [r] at *; linarith⟩
  have hg := H hV hb hz (half_pos hpos) ha hb' (fun w hw hd => (hs w (near w hw hd)).1) (fun w hw hd => (hs w (near w hw hd)).2)
  apply hg.trans
  change C*(A/(r/2)+r/2*B)≤(2*C+1)*(r⁻¹*A+r*B)
  have pa : 0≤r⁻¹*A := mul_nonneg (inv_nonneg.mpr hpos.le) ha
  have pb : 0≤r*B := mul_nonneg hpos.le hb'
  have lhs : C*(A/(r/2)+r/2*B) = 2*C*(r⁻¹*A)+(C/2)*(r*B) := by ring
  rw [lhs,mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right (by linarith) pa) (mul_le_mul_of_nonneg_right (by linarith) pb)

private theorem arc_bound {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper) (hb : ∀ x : ℝ, V x=0)
    {R C : ℝ} (hR : 0<R) (hC : 0≤C)
    (hg : ∀ z∈closedUpper, ‖z‖=R → ‖fderivWithin ℝ V closedUpper z‖≤C)
    {z : ℂ} (hz : z∈closedUpper) (hn : ‖z‖=R) : ‖V z‖≤C*R*π := by
  let S := Icc (0:ℝ) π
  have normray (a : ℝ) : ‖polarRay R a‖=R := by rw [polarRay,norm_mul,Complex.norm_of_nonneg hR.le,unitPhase_norm,mul_one]
  have hmap : MapsTo (polarRay R) S closedUpper := by
    intro a ha; change 0≤(polarRay R a).im
    rw [show (polarRay R a).im=R*Real.sin a by simp [polarRay,unitPhase,Complex.exp_mul_I,←Complex.ofReal_sin,←Complex.ofReal_cos]]
    exact mul_nonneg hR.le (sin_nonneg_of_nonneg_of_le_pi ha.1 ha.2)
  have dr (a : ℝ) : HasDerivAt (polarRay R) (I*polarRay R a) a := by
    have H := ((hasDerivAt_id (a:ℂ)).mul_const I).cexp.comp_ofReal
    unfold polarRay unitPhase
    convert H.const_mul (R:ℂ) using 1
    · rfl
    · simp [id_eq]; ring
  have hd (a : ℝ) (ha : a∈S) := (h.differentiableOn (by simp) _ (hmap ha)).hasFDerivWithinAt.comp_hasDerivWithinAt a (dr a).hasDerivWithinAt hmap
  have hd' (a : ℝ) (ha : a∈S) : ‖(fderivWithin ℝ V closedUpper (polarRay R a)) (I*polarRay R a)‖≤C*R :=
    ((fderivWithin ℝ V closedUpper _).le_opNorm _).trans (by rw [norm_mul,Complex.norm_I,one_mul,normray]; exact mul_le_mul_of_nonneg_right (hg _ (hmap ha) (normray a)) hR.le)
  have hθ := Complex.arg_nonneg_iff.mpr (show 0≤z.im from hz)
  have hθ' := Complex.arg_le_pi z
  have H := (convex_Icc (0:ℝ) π).norm_image_sub_le_of_norm_hasDerivWithin_le hd hd'
    (left_mem_Icc.mpr pi_pos.le) ⟨hθ,hθ'⟩
  change ‖V (polarRay R z.arg)-V (polarRay R 0)‖≤_ at H
  rw [show polarRay R 0=(R:ℂ) by simp [polarRay,unitPhase],hb,sub_zero,
    show polarRay R z.arg=z by rw [←hn]; exact Complex.norm_mul_exp_arg_mul_I z,sub_zero,Real.norm_eq_abs,abs_of_nonneg hθ] at H
  exact H.trans (mul_le_mul_of_nonneg_left hθ' (mul_nonneg hC hR.le))

/-- Lemma 2.2(b). Both bounds hold uniformly for r>1, with one constant
depending only on the cubic forcing constant, for every bounded V. -/
theorem dirichlet_cubic_decay {B : ℝ} (hB : 0≤B) :
    ∃ C>0, ∀ V : ℂ → ℂ, ContDiffOn ℝ ∞ V closedUpper → (∀ x : ℝ, V x=0) →
      (∃ M≥0, ∀ w∈upper, ‖V w‖≤M) →
      (∀ w∈upper, ‖Laplacian.laplacian V w‖≤B/(1+‖w‖)^3) →
      ∀ z∈closedUpper, 1<‖z‖ →
        ‖V z‖≤C*(1+Real.log ‖z‖)/‖z‖ ∧
        ‖fderivWithin ℝ V closedUpper z‖≤C*(1+Real.log ‖z‖)/‖z‖^2 := by
  obtain ⟨K,hK,H⟩ := dirichlet_gradient_cubic hB
  let C := K+π*K+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro V hV hb hm hl z hz hr
  have hg := H hV hb hm hl
  let r := ‖z‖
  have hpos : 0<r := zero_lt_one.trans hr
  have hp : 0≤1+Real.log r := by linarith [Real.log_nonneg hr.le]
  have hh := arc_bound hV hb hpos (show 0≤K*(1+Real.log r)/r^2 by positivity)
    (fun w hw hn => by simpa only [hn] using hg w hw (hn.symm ▸ hr)) hz rfl
  constructor
  · apply hh.trans
    calc
      _ = (π*K)*(1+Real.log r)/r := by field_simp <;> ring
      _ ≤ C*(1+Real.log r)/r := by gcongr; dsimp [C]; linarith
  · apply (hg z hz hr).trans
    change K*(1+Real.log r)/r^2≤C*(1+Real.log r)/r^2
    gcongr; dsimp [C]; linarith [mul_nonneg Real.pi_pos.le hK]

end Liu
