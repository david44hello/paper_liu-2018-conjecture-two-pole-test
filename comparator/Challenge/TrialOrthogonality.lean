import Challenge.TrialIntegral
import Challenge.QuotientDomain
import Challenge.PickSums
import Challenge.RadialEnergy

/- Frozen input: Liu/TrialOrthogonality.lean -/
noncomputable section
open Set MeasureTheory Complex Real Filter
open scoped Topology ComplexConjugate InnerProductSpace
namespace Liu

section
variable {F G : ℂ → ℂ} {η C : ℝ} (h : TrialWindow F G η C)
include h
def TrialWindow.trialInput (F G : ℂ → ℂ) (d : ℝ) (z : ℂ) := F z-(d:ℂ)*G z
end

section
variable {F G : ℂ → ℂ} {η C : ℝ} (h : TrialWindow F G η C)
include h
open TrialWindow
theorem TrialWindow.trial_difference_limit (hF : DifferentiableOn ℂ F upper)
    (hlog : MemLp (logInput F) 2 upperArea)
    (hG : asL2 G=asL2 (logInput F)-project (asL2 (logInput F))) :
    Tendsto (fun d : ℝ => ((∫ z, ‖trialInput F G d z‖^(2+d) ∂upperArea)-
      ∫ z, ‖F z‖^(2+d) ∂upperArea)/d^2) (𝓝[≠] 0) (𝓝 (-energy G)) := by sorry
end

end Liu
end
