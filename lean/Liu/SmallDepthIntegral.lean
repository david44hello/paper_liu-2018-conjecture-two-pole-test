module

public import Liu.SmallDepthFlux

@[expose] public section

noncomputable section
open Set Real MeasureTheory
namespace Liu

/-- The integrated conclusion of Lemma 5.4 for any pair of allowed depths. -/
theorem small_depth_flux_integral {s γ u v : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0<u)
    (huv : u≤v) (hv : v≤1/4) :
    (∫ t in u..v, |flux s γ t|)≤(2^34/(Certificate.smallMass s)^2)*v*(2+log (1/v)) := by
  let A := (2:ℝ)^34/(Certificate.smallMass s)^2
  have hA : 0≤A := by dsimp [A]; positivity
  have hpoint (t : ℝ) (ht : t∈Icc u v) : |flux s γ t|≤A*log (1/t)+A := by
    apply (small_depth_flux_estimate s γ t hg (hu.trans_le ht.1) (ht.2.trans hv)).trans_eq
    change A*(1+log (1/t))=_
    ring
  apply (log_majorant_integral hu huv (by linarith) hA hA (depth_flux_identity s γ hg u v hu huv).1.abs hpoint).trans_eq
  dsimp [A]; ring

end Liu
