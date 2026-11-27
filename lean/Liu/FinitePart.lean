module

public import Liu.Projection
public import Liu.CoordinateReduction

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Liu

def finitePartExists (S : ℂ → ℂ) : Prop :=
  (∀ R : ℝ, 0<R → IntegrableOn (fun z => k₀*‖S z‖^2-‖field S z‖^2) (halfDisc R) area) ∧
    ∃ D : ℝ, Tendsto (truncatedDeficit S) atTop (𝓝 D)

theorem finite_part_limit {S : ℂ → ℂ} (h : finitePartExists S) :
    Tendsto (truncatedDeficit S) atTop (𝓝 (deficit S)) :=
  tendsto_nhds_limUnder h.2

def energy (F : ℂ → ℂ) : ℝ := ‖asL2 F‖^2
def residual (F : ℂ → ℂ) : ℝ :=
  ‖asL2 (logInput F) - project (asL2 (logInput F))‖^2 - k₀*energy F

theorem Pair.slope_from_energy_limits (p : Pair)
    (hden : Tendsto (fun ε => ε*energy (critical p ε)) (𝓝[>] 0) (𝓝 (p.mass^2/2)))
    (hnum : Tendsto (fun ε => residual (critical p ε)) (𝓝[>] 0) (𝓝 (k₀*p.mass^2-deficit p.value))) :
    p.expansion := by
  constructor
  · filter_upwards [self_mem_nhdsWithin (a := (0:ℝ)) (s := Ioi 0)] with ε hε
    exact p.critical_domain hε
  · have hp := p.mass_pos
    have h := hnum.div hden (by positivity : p.mass^2/2 ≠ 0)
    have hs : (k₀*p.mass^2-deficit p.value)/(p.mass^2/2) = p.slope := by
      unfold Pair.slope
      field_simp
    rw [hs] at h
    apply Filter.Tendsto.congr' _ h
    filter_upwards [self_mem_nhdsWithin (a := (0:ℝ)) (s := Ioi 0)] with ε hε
    have hn := (p.critical_domain hε).2.2
    change 0<ε at hε
    dsimp [residual,energy,quotient]
    field_simp [hn.ne',hε.ne']

/-- Uses the four explicit coordinate symmetries and the two energy limits; separately
records existence of the actual finite part to rule out default values of a bare limit. -/
theorem conditional_two_pole_test (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) (hcoinc : coincidentDeficit)
    (hsmall : smallMassDeficit) (hI : FinitePartInvariances)
    (hfinite : finitePartExists p.value)
    (hden : Tendsto (fun ε => ε*energy (critical p ε)) (𝓝[>] 0) (𝓝 (p.mass^2/2)))
    (hnum : Tendsto (fun ε => residual (critical p ε)) (𝓝[>] 0) (𝓝 (k₀*p.mass^2-deficit p.value))) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2 < deficit p.value ∧ p.slope < 0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → p.quotientDomain ε ∧ quotient (critical p ε) < k₀ := by
  have hd := pair_deficit_of_inputs p hbox hflux h54 hE4 hcoinc hsmall (representation_of_invariances hI)
  exact ⟨finite_part_limit hfinite,hd,p.eventually_below_of_deficit (p.slope_from_energy_limits hden hnum) hd⟩

end Liu
