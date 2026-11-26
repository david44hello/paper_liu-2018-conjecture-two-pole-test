import Challenge.FluxDecomposition

/- Frozen input: Liu/EdgeConvolution.lean -/
noncomputable section
open Set MeasureTheory Real
namespace Liu

def depthPoisson (u x : ℝ) (h : ℂ → ℂ) : ℂ :=
  (1/π:ℝ) • ∫ Y in Ioi u, ∫ X : ℝ, (poissonLine x (Y-u) X:ℂ)*h ⟨X,Y⟩

theorem isolatedTrace_is_convolution (u x : ℝ) {w : ℂ} (hw : w.im<0) {m : ℝ} (hm : 0 < m) :
    depthPoisson u x (fun Z => ((m/‖Z-(w+(u:ℂ)*Complex.I)‖^2:ℝ):ℂ)) =
      ((m*isolatedTrace w.re (-w.im) x:ℝ):ℂ) := by sorry

def depthPoissonReal (u x : ℝ) (h : ℂ → ℝ) : ℝ :=
  (1/π) * ∫ Y in Ioi u, ∫ X : ℝ, poissonLine x (Y-u) X*h ⟨X,Y⟩

theorem edge_trace_components {s γ u : ℝ} (hg : γ ∈ Icc 0 (π/2)) (hu : 0<u) (x : ℝ) :
    let H := crossSource (normalMass s) (direction γ)
    (edgeCrossTrace s γ u x).re = depthPoissonReal u x (fun w => (H w).re) ∧
      (edgeCrossTrace s γ u x).im = depthPoissonReal u x (fun w => (H w).im) := by sorry

end Liu
end
