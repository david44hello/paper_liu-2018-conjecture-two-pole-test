module

public import Challenge.Pick

@[expose] public section

/- Frozen input: Liu/Bergman.lean -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Liu
open scoped Liu


def upperArea : Measure ℂ := area.restrict upper

abbrev PlaneL2 := Lp ℂ 2 upperArea

def analyticVectors : Set PlaneL2 :=
  {x | ∃ (f : ℂ → ℂ) (h : MemLp f 2 upperArea), DifferentiableOn ℂ f upper ∧ x = h.toLp f}

def analyticSubspace : Submodule ℂ PlaneL2 := (Submodule.span ℂ analyticVectors).topologicalClosure

def project : PlaneL2 →L[ℂ] PlaneL2 := (Submodule.span ℂ analyticVectors).topologicalClosure.starProjection

def asL2 (f : ℂ → ℂ) : PlaneL2 := by
  classical
  exact if h : MemLp f 2 upperArea then h.toLp f else 0

def logInput (f : ℂ → ℂ) (z : ℂ) : ℂ := f z * (Real.log ‖f z‖ : ℂ)

def quotient (f : ℂ → ℂ) : ℝ :=
  let input := asL2 (logInput f)
  ‖input - project input‖^2 / ‖asL2 f‖^2

def critical (p : Pair) (ε : ℝ) (z : ℂ) : ℂ := (p.value z) ^ ((1+ε:ℝ):ℂ)

def Pair.slope (p : Pair) : ℝ := 2*(k₀-deficit p.value / p.mass^2)

def Pair.quotientDomain (p : Pair) (ε : ℝ) : Prop :=
  MemLp (critical p ε) 2 upperArea ∧ MemLp (logInput (critical p ε)) 2 upperArea ∧
    0 < ‖asL2 (critical p ε)‖

end Liu
end
