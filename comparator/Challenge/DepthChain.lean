import Challenge.ReciprocalTail

/- Frozen input: Liu/DepthChain.lean -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Liu

theorem depth_chain_criterion {s γ b : ℝ} (hg : γ ∈ Icc 0 (Real.pi/2))
    (cluster : deepCluster) (hf : Certificate.fluxIdentity)
    (v : ℕ → ℝ) (n : ℕ) (hv : ∀ k, 0 < v k) (inc : Monotone v)
    (htail : ∀ t : ℝ, v n ≤ t → IntegrableOn (flux s γ) (Ioi t))
    (top : ∀ t : ℝ, v n ≤ t → (∫ x in Ioi t, flux s γ x) < singleConstant-k₀)
    (cells : ∀ k < n, ∀ t ∈ Icc (v k) (v (k+1)),
      (∫ x in t..v (k+1),flux s γ x) +
        (∑ j ∈ Finset.Ico (k+1) n, ∫ x in v j..v (j+1),flux s γ x) +
        (∫ x in Ioi (v n),flux s γ x) < singleConstant-k₀)
    (endpoint : b ≤ (singleConstant-k₀) - ((∑ j ∈ Finset.Ico 0 n, ∫ x in v j..v (j+1),flux s γ x) +
        ∫ x in Ioi (v n),flux s γ x)) :
    (∀ t : ℝ, v 0 ≤ t → 0 < margin s γ t) ∧ b ≤ margin s γ (v 0) := by sorry

end Liu
end
