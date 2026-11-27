module

public import Challenge.Reproducing

@[expose] public section

/- Frozen input: Liu/ProjectionKernel.lean -/
noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace Liu

def bergmanIntegral (h : ℂ → ℂ) (z : ℂ) := ∫ w, h w*conj (bergmanKernel z w) ∂upperArea

theorem projection_has_kernel {h : ℂ → ℂ} (hh : MemLp h 2 upperArea) :
    ∃ g : ℂ → ℂ, ∃ hg : MemLp g 2 upperArea, DifferentiableOn ℂ g upper ∧
      project (hh.toLp h) = hg.toLp g ∧ EqOn g (bergmanIntegral h) upper := by sorry

end Liu
end
