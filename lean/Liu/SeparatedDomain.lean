import Liu.SeparatedPhysical

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu.PickChart

def below (P : PickChart) (w : ℂ) : Prop :=
  (P.left w).im < 0 ∧ (P.right w).im < 0 ∧ (P.zeroNode w).im < 0

/-- The two conditions express lower nodes and upper partners, with each
partner at w the conjugate of its lower-node expression at conj w. -/
def domain (P : PickChart) (D : Set ℂ) : Set ℂ :=
  {w | (w∈D ∧ P.below w) ∧ (conj w∈D ∧ P.below (conj w))}

theorem regular_domain (P : PickChart) {D : Set ℂ} (hD : IsOpen D)
    (hm : DifferentiableOn ℂ P.mass D) (hl : DifferentiableOn ℂ P.left D)
    (hr : DifferentiableOn ℂ P.right D) : P.Regular (P.domain D) := by
  let A := {w | w ∈ D ∧ P.below w}
  have ho : DifferentiableOn ℂ P.zeroNode D :=
    (hm.mul hr).add ((hm.const_sub 1).mul hl)
  have hA : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro w hw
    obtain ⟨hd,h₁,h₂,h₃⟩ := hw
    have H (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f D) (hn : (f w).im<0) :
        ∀ᶠ v in 𝓝 w, (f v).im<0 :=
      (Complex.continuous_im.continuousAt.comp (hf.differentiableAt (hD.mem_nhds hd)).continuousAt).eventually_lt
        continuousAt_const hn
    filter_upwards [hD.mem_nhds hd,H _ hl h₁,H _ hr h₂,H _ ho h₃] with v hv h₁ h₂ h₃ using ⟨hv,h₁,h₂,h₃⟩
  have hsub : P.domain D ⊆ D := fun w hw => hw.1.1
  exact ⟨hA.inter (hA.preimage (by fun_prop : Continuous (conj : ℂ → ℂ))),
    fun w hw => ⟨hw.2,by simpa only [Complex.conj_conj] using hw.1⟩,
    hm.mono hsub,hl.mono hsub,hr.mono hsub,fun w hw => hw.1.2.1,
    fun w hw => hw.1.2.2.1,fun w hw => hw.1.2.2.2⟩

/-- The same lower-node and upper-partner tests work at coincident poles. -/
theorem separated_extension (P : PickChart) {D E : Set ℂ} (hD : IsOpen D)
    (hm : DifferentiableOn ℂ P.mass D) (hl : DifferentiableOn ℂ P.left D)
    (hr : DifferentiableOn ℂ P.right D) (hE : E ⊆ P.domain D) :
    AnalyticOnNhd ℂ P.fluxExtension E ∧
    ∀ r a : ℝ, (r:ℂ)∈E → P.mass r=(a:ℂ) → 0<a → a<1 →
      P.fluxExtension r=(boundaryFlux (P.realSum r a):ℂ) := by
  have h := P.regular_domain hD hm hl hr
  exact ⟨h.flux_analytic.mono hE,fun r a hmem he h₀ h₁ => h.flux_agrees (hE hmem) he h₀ h₁⟩

end Liu.PickChart
