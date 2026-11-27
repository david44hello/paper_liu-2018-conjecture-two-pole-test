module

public import Liu.ContourAnalytic

@[expose] public section

noncomputable section
open Set Filter Real Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace Liu

theorem WindowFamily.continuation {U} (W : WindowFamily U) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F U ∧ ∀ w∈U, ∀ γ : RealContour, γ.admissible (W.L w) (W.Q w) →
      F w=γ.integral (W.H w)/(Real.pi:ℂ) := by
  classical
  let path := fun w => if hw : w∈U then Classical.choose (RealContour.exists_admissible _ _ (W.clear w hw)) else straightContour
  have hp {w : ℂ} (hw : w∈U) : (path w).admissible (W.L w) (W.Q w) := by
    dsimp [path]; rw [dif_pos hw]; exact Classical.choose_spec (RealContour.exists_admissible _ _ (W.clear w hw))
  let F := fun w => (path w).integral (W.H w)/(Real.pi:ℂ)
  have agree (w : ℂ) (hw : w∈U) (γ : RealContour) (hg : γ.admissible (W.L w) (W.Q w)) :
      F w=γ.integral (W.H w)/(Real.pi:ℂ) := by dsimp only [F]; rw [W.contour_independent hw (path w) γ (hp hw) hg]
  refine ⟨F,?_,agree⟩
  intro w hw
  let γ := path w
  have hin : w∈W.pathDomain γ := ⟨hw,hp hw⟩
  have hnear : F =ᶠ[𝓝 w] fun v => γ.integral (W.H v)/(Real.pi:ℂ) := by
    filter_upwards [(W.pathDomain_open γ).mem_nhds hin] with v hv using agree v hv.1 γ hv.2
  exact (((W.analytic_contour γ) w hin).div_const (c:=(Real.pi:ℂ))).congr hnear.symm

def massStrip : Set ℂ := {s | |s.im|<Real.pi/2}

theorem stripMass_diff : DifferentiableOn ℂ stripMass massStrip := by
  intro s hs
  change |s.im| < π/2 at hs
  have hr : 0<(Complex.exp s).re := by
    rw [Complex.exp_re]; exact mul_pos (Real.exp_pos _) (cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hs).1],(abs_lt.mp hs).2⟩)
  have hn : 1+Complex.exp s ≠ 0 := by intro e; have h := congrArg Complex.re e; simp at h; linarith
  unfold stripMass
  exact ((Complex.differentiableAt_exp.const_add 1).inv hn).differentiableWithinAt

def stripFamily {γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0<u) : WindowFamily massStrip where
  lower i s := windowLower (stripMass s) γ u i
  partner i s := windowUpper (stripMass s) γ u i
  mass₁ := stripMass
  mass₂ s := 1-stripMass s
  openSet := isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  dl i := by
    fin_cases i
    · exact differentiableOn_const _
    · exact differentiableOn_const _
    · exact (stripMass_diff.mul_const _).const_add _
  dq i := by
    fin_cases i
    · exact differentiableOn_const _
    · exact differentiableOn_const _
    · exact (stripMass_diff.mul_const _).const_add _
  da := stripMass_diff
  db := stripMass_diff.const_sub 1
  clear _ hw _ _ := strip_no_collision hw hg hu _ _

theorem strip_physical_config {γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0<u) (r : ℝ) :
    let W := stripFamily hg hu
    let P := normalPair r γ u hg hu
    W.L r=P.tailNodes ∧ W.Q r=(fun i => conj (P.tailNodes i)) ∧
      W.mass₁ r=(P.a₁:ℂ) ∧ W.mass₂ r=(P.a₂:ℂ) := by
  have hm : stripMass r=(normalMass r:ℂ) := by simp [stripMass,normalMass,one_div,Complex.ofReal_exp]
  refine ⟨?_,?_,hm,?_⟩
  · funext i; fin_cases i <;> simp [WindowFamily.L,stripFamily,windowLower,Pair.tailNodes,Pair.weightedZero,normalPair,hm] <;> ring
  · funext i; fin_cases i <;> simp [WindowFamily.Q,stripFamily,windowUpper,Pair.tailNodes,Pair.weightedZero,normalPair,hm] <;> ring
  · change 1-stripMass r=_; rw [hm]; simp [normalPair]

/-- Lemma D.2(a), for any configuration satisfying the geometric
noncollision condition, with all locally absolutely continuous contours. -/
theorem admissible_contour_independence (P Q : Fin 3 → ℂ) (a b : ℂ)
    (hx : ∀ i j, ¬rayCollision (P i) (Q j)) :
    (∃ γ : RealContour, γ.admissible P Q) ∧
      (∀ γ : RealContour, γ.admissible P Q →
        Integrable (fun t => totalDensity P Q a b (γ.path t)*deriv γ.path t)) ∧
      ∀ γ η : RealContour, γ.admissible P Q → η.admissible P Q →
        γ.integral (totalDensity P Q a b)=η.integral (totalDensity P Q a b) := by
  let W : WindowFamily univ := ⟨fun i _ => P i,fun i _ => Q i,fun _ => a,fun _ => b,isOpen_univ,
    fun _ => differentiableOn_const _,fun _ => differentiableOn_const _,differentiableOn_const _,differentiableOn_const _,
    fun _ _ => hx⟩
  exact ⟨RealContour.exists_admissible P Q hx,fun γ h => (W.contour_dominated γ).integrable (show (0:ℂ)∈W.pathDomain γ from ⟨mem_univ _,h⟩),
    fun γ η hg he => W.contour_independent (w:=0) (mem_univ _) γ η hg he⟩

/-- Lemma D.2(b,c). Every point of the open strip admits a contour.
The integral of the explicit continued density, on any admissible contour,
defines one holomorphic extension of the physical flux. -/
theorem mass_window_continuation {γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0<u) :
    let W := stripFamily hg hu
    (∀ s∈massStrip, ∀ i j, ¬rayCollision (W.L s i) (W.Q s j)) ∧
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F massStrip ∧ (∀ r : ℝ, F r=(flux r γ u:ℂ)) ∧
      ∀ s∈massStrip, (∃ η : RealContour, η.admissible (W.L s) (W.Q s)) ∧
        ∀ η : RealContour, η.admissible (W.L s) (W.Q s) →
          F s=η.integral (W.H s)/(Real.pi:ℂ) := by
  let W := stripFamily hg hu
  obtain ⟨F,hF,he⟩ := W.continuation
  refine ⟨W.clear,F,hF,?_,fun s hs => ⟨RealContour.exists_admissible _ _ (W.clear _ hs),he _ hs⟩⟩
  intro r
  let P := normalPair r γ u hg hu
  have hm : P.a₁+P.a₂=1 := by simp [P,normalPair]
  obtain ⟨hl,hq,ha,hb⟩ := strip_physical_config hg hu r
  change W.L r=P.tailNodes at hl
  change W.Q r=(fun i => conj (P.tailNodes i)) at hq
  have hreal : straightContour.admissible (W.L r) (W.Q r) := by
    rw [hl,hq]
    exact fun x => ⟨fun i _ => by simpa [straightContour] using P.tailNodes_below i,
      fun j _ => by simpa [straightContour] using P.tailNodes_below j⟩
  have hr : (r:ℂ)∈massStrip := by simp [massStrip,Real.pi_pos]
  rw [he _ hr straightContour hreal]
  change (∫ x : ℝ, totalDensity (W.L r) (W.Q r) (W.mass₁ r) (W.mass₂ r) (x:ℂ)*deriv (fun t : ℝ => (t:ℂ)) x)/(Real.pi:ℂ)=_
  rw [hl,hq,ha,hb]
  have hd (x : ℝ) : deriv (fun t : ℝ => (t:ℂ)) x=1 :=
    (show HasDerivAt (fun t : ℝ => (t:ℂ)) 1 x from Complex.ofRealCLM.hasDerivAt).deriv
  simp_rw [hd,mul_one]
  change pairedBoundaryFlux P.tailNodes (fun i => conj (P.tailNodes i)) P.a₁ P.a₂=(flux r γ u:ℂ)
  rw [P.pairedBoundaryFlux_actual hm]
  have hval : P.toPick.value=normalSum r γ u := normalPair_value r γ u hg hu
  rw [hval]; rfl

end Liu
