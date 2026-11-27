module

public import Liu.SeparatedDomain
public import Liu.ReciprocalDisc
public import Liu.ChebyshevAlias

@[expose] public section

noncomputable section
open Real Set
open scoped ComplexConjugate Topology
namespace Liu

/-- An affine line through the three interpolation coordinates. A coordinate
held fixed has slope zero. For a logarithmic angular row, g is log γ. -/
structure CellLine where
  s₀ : ℝ
  s₁ : ℝ
  g₀ : ℝ
  g₁ : ℝ
  y₀ : ℝ
  y₁ : ℝ
  logAngle : Bool

def CellLine.s (L : CellLine) (w : ℂ) : ℂ := L.s₀+(L.s₁:ℂ)*w
def CellLine.angle (L : CellLine) (w : ℂ) : ℂ :=
  let g := (L.g₀:ℂ)+(L.g₁:ℂ)*w
  if L.logAngle then Complex.exp g else g

def CellLine.y (L : CellLine) (w : ℂ) : ℂ := L.y₀+(L.y₁:ℂ)*w

def CellLine.realAngle (L : CellLine) (r : ℝ) : ℝ :=
  if L.logAngle then exp (L.g₀+L.g₁*r) else L.g₀+L.g₁*r

def CellLine.depth (L : CellLine) (u : ℝ) (w : ℂ) : ℂ := (u:ℂ)*Complex.exp (L.y w-1)

def reciprocalScale : ℝ := exp (-(1/2))/2

def CellLine.reciprocal (L : CellLine) (w : ℂ) : ℂ := (reciprocalScale:ℂ)*(1-L.y w)

def CellLine.nodes (L : CellLine) (d v : ℂ → ℂ) : PickChart where
  mass w := 1/(1+Complex.exp (L.s w))
  left w := -d w*Complex.I
  right w := -d w*Complex.I+v w*Complex.exp (-L.angle w*Complex.I)

def CellLine.massDomain (L : CellLine) : Set ℂ := {w | 1+Complex.exp (L.s w) ≠ 0}

theorem CellLine.angle_real (L : CellLine) (r : ℝ) : L.angle r = (L.realAngle r:ℂ) := by
  cases h : L.logAngle <;> simp [CellLine.angle,CellLine.realAngle,h,Complex.ofReal_exp]

theorem CellLine.mass_real (L : CellLine) (d v : ℂ → ℂ) (r : ℝ) :
    (L.nodes d v).mass r = (normalMass (L.s₀+L.s₁*r):ℂ) := by
  simp [CellLine.nodes,normalMass,CellLine.s,Complex.ofReal_exp]

theorem CellLine.mass_domain_real (L : CellLine) (r : ℝ) : (r:ℂ)∈L.massDomain := by
  have h : (0:ℝ)<1+exp (L.s₀+L.s₁*r) := by positivity
  simpa [CellLine.massDomain,CellLine.s,Complex.ofReal_exp] using Complex.ofReal_ne_zero.mpr h.ne'

theorem CellLine.regular (L : CellLine) {d v : ℂ → ℂ} (hd : Differentiable ℂ d) (hv : Differentiable ℂ v) :
    (L.nodes d v).Regular ((L.nodes d v).domain L.massDomain) := by
  have hA : Differentiable ℂ L.angle := by
    intro w; unfold CellLine.angle; split <;> fun_prop
  have hD : IsOpen L.massDomain := isOpen_ne_fun (by unfold CellLine.s; fun_prop) continuous_const
  apply PickChart.regular_domain _ hD
  · intro w hw
    change DifferentiableWithinAt ℂ (fun w => 1/(1+Complex.exp (L.s w))) _ _
    have hz : 1+Complex.exp (L.s w) ≠ 0 := hw
    have hs : Differentiable ℂ L.s := by unfold CellLine.s; fun_prop
    apply DifferentiableAt.differentiableWithinAt
    exact (differentiableAt_const 1).div ((Complex.differentiableAt_exp.comp w (hs w)).const_add 1) hz
  · change DifferentiableOn ℂ (fun w => -d w*Complex.I) _
    fun_prop
  · change DifferentiableOn ℂ (fun w => -d w*Complex.I+v w*Complex.exp (-L.angle w*Complex.I)) _
    fun_prop

theorem CellLine.depth_real (L : CellLine) (u r : ℝ) :
    L.depth u r = ((u*exp (L.y₀+L.y₁*r-1):ℝ):ℂ) := by
  simp [CellLine.depth,CellLine.y,Complex.ofReal_exp]

theorem CellLine.reciprocal_real (L : CellLine) (r : ℝ) :
    L.reciprocal r = ((reciprocalScale*(1-(L.y₀+L.y₁*r)):ℝ):ℂ) := by
  simp [CellLine.reciprocal,CellLine.y]

def CellLine.cellNodes (L : CellLine) (u : ℝ) := L.nodes (L.depth u) (fun _ => 1)
def CellLine.topNodes (L : CellLine) := L.nodes (fun _ => 1) L.reciprocal

theorem CellLine.cell_regular (L : CellLine) (u : ℝ) :
    (L.cellNodes u).Regular ((L.cellNodes u).domain L.massDomain) :=
  L.regular (by unfold CellLine.depth CellLine.y; fun_prop) (by fun_prop)

theorem CellLine.top_regular (L : CellLine) :
    L.topNodes.Regular (L.topNodes.domain L.massDomain) :=
  L.regular (by fun_prop) (by unfold CellLine.reciprocal CellLine.y; fun_prop)

/-- On an ordinary depth cell, for any of the three axes, lower nodes and
upper partners suffice on the tested set, including its boundary. -/
theorem cell_flux_separated (L : CellLine) (u : ℝ) {E : Set ℂ}
    (hE : E ⊆ (L.cellNodes u).domain L.massDomain) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F E ∧ ∀ r : ℝ, (r:ℂ) ∈ E →
      F r = ((u*exp (L.y₀+L.y₁*r-1)*flux (L.s₀+L.s₁*r) (L.realAngle r)
        (u*exp (L.y₀+L.y₁*r-1)):ℝ):ℂ) := by
  have h := L.cell_regular u
  have hd : Differentiable ℂ (L.depth u) := by unfold CellLine.depth CellLine.y; fun_prop
  refine ⟨fun w => L.depth u w*(L.cellNodes u).fluxExtension w,
    ((hd.differentiableOn.analyticOnNhd h.isOpen).mul h.flux_analytic).mono hE,?_⟩
  intro r hr
  let s := L.s₀+L.s₁*r
  have hp := Certificate.normalMass_pos s
  have h₁ : normalMass s < 1 := by linarith [Certificate.complement_normalMass s,Certificate.normalMass_pos (-s)]
  dsimp only
  have he : (L.cellNodes u).realSum r (normalMass s) =
      normalSum s (L.realAngle r) (u*exp (L.y₀+L.y₁*r-1)) := by
    funext z
    simp [PickChart.realSum,CellLine.cellNodes,CellLine.nodes,L.angle_real,L.depth_real,
      normalSum,direction]
  rw [h.flux_agrees (hE hr) (L.mass_real _ _ r) hp h₁,L.depth_real]
  change _ * (boundaryFlux ((L.cellNodes u).realSum r (normalMass s)):ℂ) = _
  rw [he,←Complex.ofReal_mul]
  rfl

theorem CellLine.top_agrees (L : CellLine) {r : ℝ}
    (hr : (r:ℂ) ∈ L.topNodes.domain L.massDomain) :
    L.topNodes.fluxExtension r=(boundaryFlux
      (unitDepthSum (L.s₀+L.s₁*r) (L.realAngle r) (reciprocalScale*(1-(L.y₀+L.y₁*r)))):ℂ) := by
  let s := L.s₀+L.s₁*r
  have hp := Certificate.normalMass_pos s
  have h₁ : normalMass s < 1 := by linarith [Certificate.complement_normalMass s,Certificate.normalMass_pos (-s)]
  rw [L.top_regular.flux_agrees hr (L.mass_real _ _ r) hp h₁]
  congr 2
  funext z
  simp [PickChart.realSum,CellLine.topNodes,CellLine.nodes,L.angle_real,L.reciprocal_real,
    unitDepthSum,direction]

end Liu
