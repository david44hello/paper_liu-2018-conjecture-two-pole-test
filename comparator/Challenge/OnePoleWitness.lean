import Challenge.WitnessClaim
import Challenge.SinglePoleEvaluation
import Mathlib.Analysis.Complex.RemovableSingularity

/- Frozen input: Liu/OnePoleWitness.lean -/
noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped Topology ComplexConjugate Interval
namespace Liu

def omegaCorrection := dslope (fun z : ℂ => Complex.log (z+Complex.I)) Complex.I

def singleWitness (z : ℂ) := ((π/2:ℝ):ℂ)+omegaCorrection z

theorem omegaCorrection_regular :
    DifferentiableOn ℂ omegaCorrection {z : ℂ | -1<z.im} := by sorry

theorem singleWitness_isWitness : isWitness singleWitness := by sorry

theorem omegaCorrection_sup : sSup (Set.range (fun z : {w : ℂ // 0≤w.im} => ‖omegaCorrection z‖))=log 2 := by sorry

end Liu
end
