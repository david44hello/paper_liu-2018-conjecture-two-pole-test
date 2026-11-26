import Challenge.LogTailKernel

/- Frozen input: Liu/TailPhysical.lean -/
noncomputable section
open Set Real Polynomial
open scoped ComplexConjugate
namespace Liu

def Pair.weightedZero (P : Pair) : ℂ := (P.a₁:ℂ)*P.w₂+(P.a₂:ℂ)*P.w₁

def Pair.tailNodes (P : Pair) : Fin 3 → ℂ := ![P.w₁,P.w₂,P.weightedZero]

theorem Pair.tail_subtraction_agrees (P : Pair) (hm : P.a₁+P.a₂=1) (x : ℝ) :
    let h := fun S : ℂ → ℂ => ‖field S x‖^2-k₀*‖S x‖^2
    subtractedTail P.tailNodes (fun i => conj (P.tailNodes i)) P.a₁ P.a₂ x =
      ((h P.toPick.value-P.a₁^2*h (pole 1 P.w₁)-P.a₂^2*h (pole 1 P.w₂):ℝ):ℂ) := by sorry

end Liu
end
