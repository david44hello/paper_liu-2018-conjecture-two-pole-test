import Challenge.BlendExpansion
import Challenge.RadialEnergy

/- Frozen input: Liu/SmallRemainder.lean -/
noncomputable section
open Set Real MeasureTheory Filter
open scoped ComplexConjugate Topology
namespace Liu

def smallMassRemainder (p q : ℂ) (m : ℝ) : ℝ :=
  let A := pole 1 p
  let B := pole 1 q
  let g := fun z => blendedError (A z) ((m:ℂ)*B z)
  let Δ := fun z => g z-(m:ℂ)*linearBlend (A z) (B z)
  show ℝ from -2*(∫ z, field A z*conj (Δ z) ∂upperArea).re -
    (∫ z, ‖g z‖^2 ∂upperArea) - 2*m*(∫ z, field B z*conj (g z) ∂upperArea).re

theorem smallMassRemainder_estimates {p q : ℂ} (hp : p.im<0) (hq : q.im<0) {m : ℝ} (hm : 0 < m) (hm' : m≤1/10) :
    let A := pole 1 p
    let B := pole 1 q
    let g := fun z => blendedError (A z) ((m:ℂ)*B z)
    let Δ := fun z => g z-(m:ℂ)*linearBlend (A z) (B z)
    Integrable (fun z => field A z*conj (Δ z)) upperArea ∧
    Integrable (fun z => field B z*conj (g z)) upperArea ∧
    Integrable (fun z => ‖g z‖^2) upperArea ∧
    -(m^2*(520+111*log (2/m))) ≤ smallMassRemainder p q m := by sorry

theorem smallMassRemainder_bound {p q : ℂ} (hp : p.im<0) (hq : q.im<0) {m : ℝ} (hm : 0 < m) (hm' : m≤1/10) :
    -(m^2*(520+111*log (2/m))) ≤ smallMassRemainder p q m := by sorry

end Liu
end
