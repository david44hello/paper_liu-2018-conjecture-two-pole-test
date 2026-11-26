import Liu.Pick

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Liu

def upperArea : Measure ℂ := area.restrict upper
abbrev PlaneL2 := Lp ℂ 2 upperArea

/-- Vectors represented by square-integrable holomorphic functions in the upper half-plane. -/
def analyticVectors : Set PlaneL2 :=
  {x | ∃ (f : ℂ → ℂ) (h : MemLp f 2 upperArea), DifferentiableOn ℂ f upper ∧ x = h.toLp f}

/-- Taking closed span constructs the orthogonal projection without assuming the density
or closed-representative theorem. The latter identification is a separate analytic obligation. -/
def analyticSubspace : Submodule ℂ PlaneL2 := (Submodule.span ℂ analyticVectors).topologicalClosure

def project : PlaneL2 →L[ℂ] PlaneL2 := (Submodule.span ℂ analyticVectors).topologicalClosure.starProjection

theorem project_fixes_analytic {f : ℂ → ℂ} (hf : MemLp f 2 upperArea)
    (hd : DifferentiableOn ℂ f upper) : project (hf.toLp f) = hf.toLp f := by
  have hv : hf.toLp f ∈ analyticVectors := ⟨f,hf,hd,rfl⟩
  apply Submodule.starProjection_eq_self_iff.mpr
  exact (Submodule.span ℂ analyticVectors).le_topologicalClosure (Submodule.subset_span hv)

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

/-- The punctured right-hand slope statement, with the genuine quotient and its domain. -/
def Pair.expansion (p : Pair) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0:ℝ), p.quotientDomain ε) ∧
    Tendsto (fun ε => (quotient (critical p ε)-k₀)/ε) (𝓝[>] 0) (𝓝 p.slope)

theorem Pair.eventually_below_of_deficit (p : Pair) (hexp : p.expansion)
    (hd : k₀*p.mass^2 < deficit p.value) :
    p.slope < 0 ∧ ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      p.quotientDomain ε ∧ quotient (critical p ε) < k₀ := by
  have hm : 0 < p.mass^2 := sq_pos_of_pos p.mass_pos
  have hs : p.slope < 0 := by
    have h := (lt_div_iff₀ hm).mpr hd
    unfold Pair.slope
    linarith
  refine ⟨hs, ?_⟩
  have he : ∀ᶠ ε in 𝓝[>] (0:ℝ), (quotient (critical p ε)-k₀)/ε < 0 :=
    hexp.2.eventually_lt_const hs
  have hpos : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
  have ev : ∀ᶠ ε in 𝓝[>] (0:ℝ), p.quotientDomain ε ∧ quotient (critical p ε) < k₀ := by
    filter_upwards [hexp.1,he,hpos] with ε hdom hq hε
    have := (div_lt_iff₀ hε).mp hq
    exact ⟨hdom,by linarith⟩
  obtain ⟨ε₀,h₀,hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp ev
  exact ⟨ε₀,h₀,fun ε h₁ h₂ => hsub ⟨h₁,h₂⟩⟩

end Liu
