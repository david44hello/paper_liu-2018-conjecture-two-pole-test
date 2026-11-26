import Challenge.LogTailKernel

/- Frozen input: Liu/LogTailEstimate.lean -/
noncomputable section
open Set Real Complex
namespace Liu

theorem subtracted_flux_tail_bound (P Q : Fin 3 → ℂ) (a b : ℂ) {X x : ℝ}
    (hX : 10^18≤X) (hP : ∀ i, 4*‖P i‖<X) (hQ : ∀ i, 4*‖Q i‖<X) (hx : X≤|x|) :
    ‖subtractedTail P Q a b (x:ℂ)‖ ≤
      ((8*‖a*b‖+32*(‖a‖+‖b‖)^2)*tailUpsilon P Q x^2+8*k₀*‖a*b‖)/x^2 := by sorry

theorem moved_flux_tail_bound (P Q : Fin 3 → ℂ) (a b : ℂ) (path : ℝ → ℂ) {X : ℝ}
    (hX : 10^18≤X) (hP : ∀ i, 4*‖P i‖<X) (hQ : ∀ i, 4*‖Q i‖<X)
    (hpath : ∀ x, X≤|x| → path x=(x:ℂ)) {x : ℝ} (hx : X≤|x|) :
    ‖subtractedTail P Q a b (path x)‖ ≤
      ((8*‖a*b‖+32*(‖a‖+‖b‖)^2)*tailUpsilon P Q x^2+8*k₀*‖a*b‖)/x^2 := by sorry

end Liu
end
