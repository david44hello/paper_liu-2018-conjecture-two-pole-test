import Challenge.AdmissibleContour

/- Frozen input: Liu/WindowContinuation.lean -/
noncomputable section
open Set Filter Real Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace Liu

def massStrip : Set ℂ := {s | |s.im|<Real.pi/2}

theorem stripMass_diff : DifferentiableOn ℂ stripMass massStrip := by sorry

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

theorem admissible_contour_independence (P Q : Fin 3 → ℂ) (a b : ℂ)
    (hx : ∀ i j, ¬rayCollision (P i) (Q j)) :
    (∃ γ : RealContour, γ.admissible P Q) ∧
      (∀ γ : RealContour, γ.admissible P Q →
        Integrable (fun t => totalDensity P Q a b (γ.path t)*deriv γ.path t)) ∧
      ∀ γ η : RealContour, γ.admissible P Q → η.admissible P Q →
        γ.integral (totalDensity P Q a b)=η.integral (totalDensity P Q a b) := by sorry

theorem mass_window_continuation {γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0<u) :
    let W := stripFamily hg hu
    (∀ s∈massStrip, ∀ i j, ¬rayCollision (W.L s i) (W.Q s j)) ∧
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F massStrip ∧ (∀ r : ℝ, F r=(flux r γ u:ℂ)) ∧
      ∀ s∈massStrip, (∃ η : RealContour, η.admissible (W.L s) (W.Q s)) ∧
        ∀ η : RealContour, η.admissible (W.L s) (W.Q s) →
          F s=η.integral (W.H s)/(Real.pi:ℂ) := by sorry

end Liu
end
