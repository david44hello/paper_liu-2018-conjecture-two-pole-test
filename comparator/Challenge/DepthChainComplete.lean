import Challenge.ReciprocalDisc
import Challenge.DepthChain

/- Frozen input: Liu/DepthChainComplete.lean -/
noncomputable section
open Set Real MeasureTheory
namespace Liu

theorem depth_chain_from_tests {s γ b : ℝ} (hg : γ∈Icc 0 (π/2))
    (v : ℕ → ℝ) (n : ℕ) (hv : ∀ k, 0<v k) (inc : Monotone v)
    (top : ∀ t : ℝ, v n≤t → (∫ x in Ioi t, flux s γ x) < singleConstant-k₀)
    (cells : ∀ k < n, ∀ t∈Icc (v k) (v (k+1)),
      (∫ x in t..v (k+1),flux s γ x)+
        (∑ j ∈ Finset.Ico (k+1) n, ∫ x in v j..v (j+1),flux s γ x)+
        (∫ x in Ioi (v n),flux s γ x) < singleConstant-k₀)
    (endpoint : b≤(singleConstant-k₀)-((∑ j ∈ Finset.Ico 0 n, ∫ x in v j..v (j+1),flux s γ x)+
      ∫ x in Ioi (v n),flux s γ x)) :
    (∀ t : ℝ, v 0≤t → 0 < margin s γ t) ∧ b ≤ margin s γ (v 0) := by sorry

theorem box_conclusions_from_chain_tests (B : Certificate.Box) (v : ℕ → ℝ) (n : ℕ)
    (hstart : v 0=B.depth) (hv : ∀ k, 0<v k) (inc : Monotone v)
    (tests : ∀ s γ : ℝ, B.contains s γ → γ∈Icc 0 (π/2) →
      (∀ t : ℝ, v n≤t → (∫ x in Ioi t, flux s γ x) < singleConstant-k₀) ∧
      (∀ k < n, ∀ t∈Icc (v k) (v (k+1)),
        (∫ x in t..v (k+1),flux s γ x)+
          (∑ j ∈ Finset.Ico (k+1) n, ∫ x in v j..v (j+1),flux s γ x)+
          (∫ x in Ioi (v n),flux s γ x) < singleConstant-k₀) ∧
      (B.safeLower:ℝ)≤(singleConstant-k₀)-((∑ j ∈ Finset.Ico 0 n, ∫ x in v j..v (j+1),flux s γ x)+
        ∫ x in Ioi (v n),flux s γ x)) :
    ∀ s γ : ℝ, B.contains s γ → γ∈Icc 0 (π/2) →
      (∀ t : ℝ, B.depth≤t → 0 < margin s γ t) ∧ (B.safeLower:ℝ) ≤ margin s γ B.depth := by sorry

end Liu
end
