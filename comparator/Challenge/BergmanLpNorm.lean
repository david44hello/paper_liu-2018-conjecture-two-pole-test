import Challenge.ProjectionKernel
import Challenge.LiuGammaPower

/- Frozen input: Liu/BergmanLpNorm.lean -/
noncomputable section
open Set MeasureTheory Real Complex
open scoped ENNReal Topology
namespace Liu

def bergmanLpNorm (p : ℝ) : ℝ≥0∞ :=
  ⨆ (f : ℂ → ℂ) (_ : MemLp f (ENNReal.ofReal p) upperArea)
    (_ : eLpNorm f (ENNReal.ofReal p) upperArea≠0),
    eLpNorm (bergmanIntegral f) (ENNReal.ofReal p) upperArea/eLpNorm f (ENNReal.ofReal p) upperArea

theorem bergmanLpNorm_operator_bound_iff {p M : ℝ} (hp : 1≤p) (hM : 0≤M)
    [Fact (1≤ENNReal.ofReal p)]
    (B : Lp ℂ (ENNReal.ofReal p) upperArea →L[ℂ] Lp ℂ (ENNReal.ofReal p) upperArea)
    (hB : ∀ (f : ℂ → ℂ) (hf : MemLp f (ENNReal.ofReal p) upperArea),
      ⇑(B (hf.toLp f))=ᵐ[upperArea] bergmanIntegral f) :
    bergmanLpNorm p≤ENNReal.ofReal M ↔ ‖B‖≤M := by sorry

end Liu
end
