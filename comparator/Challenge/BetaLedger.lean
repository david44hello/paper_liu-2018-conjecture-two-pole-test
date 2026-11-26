import Challenge.Beta

/- Frozen input: Liu/BetaLedger.lean -/
noncomputable section
namespace Liu.Certificate

theorem certified_numeric_bounds {b : Box} (hb : b ∈ boxes) :
    0 < b.depth ∧ b.depth ≤ 1/4 ∧ b.beta ≤ 1/2000 ∧
    285/10000 + b.beta < (b.safeLower:ℝ) := by sorry

end Liu.Certificate
end
