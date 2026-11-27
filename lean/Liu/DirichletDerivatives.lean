module

public import Liu.WeakBergman
public import Liu.WitnessClaim
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Complex.Convex

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Real Complex
open scoped Topology ContDiff InnerProductSpace ComplexConjugate
namespace Liu

def closedUpper := {z : ℂ | 0≤z.im}

theorem closedUpper_uniqueDiff : UniqueDiffOn ℝ closedUpper :=
  uniqueDiffOn_convex (convex_halfSpace_im_ge 0) ⟨I,
    mem_interior_iff_mem_nhds.mpr (mem_of_superset (upper_open.mem_nhds (show I∈upper by simp [upper]))
      (show upper⊆closedUpper from fun z h => (show 0<z.im from h).le))⟩

theorem closedUpper_nhds {z : ℂ} (hz : z∈upper) : closedUpper∈𝓝 z :=
  mem_of_superset (upper_open.mem_nhds hz) (show upper⊆closedUpper from fun z h => (show 0<z.im from h).le)

/-- Directional derivatives use the unique differential on the closed half-plane. -/
def dirPart (v : ℂ) (V : ℂ → ℂ) (z : ℂ) := fderivWithin ℝ V closedUpper z v

def dirLap (V : ℂ → ℂ) := dirPart 1 (dirPart 1 V)+dirPart I (dirPart I V)

def dirField (V : ℂ → ℂ) (z : ℂ) := -(dirPart 1 V z-I*dirPart I V z)

theorem dirPart_smooth {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper) (v : ℂ) :
    ContDiffOn ℝ ∞ (dirPart v V) closedUpper :=
  (h.fderivWithin closedUpper_uniqueDiff (by simp)).clm_apply contDiffOn_const

theorem dirPart_inside (v : ℂ) (V : ℂ → ℂ) {z : ℂ} (hz : z∈upper) :
    dirPart v V z=fderiv ℝ V z v := by rw [dirPart,fderivWithin_of_mem_nhds (closedUpper_nhds hz)]

private theorem dp2 {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper) (u v : ℂ) {z : ℂ} (hz : z∈upper) :
    dirPart u (dirPart v V) z = fderiv ℝ (fderiv ℝ V) z u v := by
  have hd := (h z (show 0≤z.im from (show 0<z.im from hz).le)).contDiffAt (closedUpper_nhds hz)
  have H : dirPart v V =ᶠ[𝓝 z] fun w => fderiv ℝ V w v :=
    by filter_upwards [upper_open.mem_nhds hz] with w hw using dirPart_inside v V hw
  rw [dirPart_inside _ _ hz,H.fderiv_eq]
  rw [fderiv_clm_apply ((hd.fderiv_right (m:=1) (by simp)).differentiableAt (by simp)) (by fun_prop)]
  simp

theorem dirLap_inside {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper) {z : ℂ} (hz : z∈upper) :
    dirLap V z=Laplacian.laplacian V z := by
  simp only [dirLap,Pi.add_apply,dp2 h _ _ hz,InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]

theorem dirField_smooth {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper) :
    ContDiffOn ℝ ∞ (dirField V) closedUpper :=
  ((dirPart_smooth h 1).sub (contDiffOn_const.mul (dirPart_smooth h I))).neg

theorem dirLap_smooth {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper) :
    ContDiffOn ℝ ∞ (dirLap V) closedUpper :=
  (dirPart_smooth (dirPart_smooth h 1) 1).add (dirPart_smooth (dirPart_smooth h I) I)

theorem dirField_dbar {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper) {z : ℂ} (hz : z∈upper) :
    dbar (dirField V) z= -(dirLap V z)/2 := by
  have hcl : z∈closedUpper := (show 0<z.im from hz).le
  have d (v : ℂ) := ((dirPart_smooth h v z hcl).contDiffAt (closedUpper_nhds hz)).differentiableAt (by simp)
  have hd := ((d 1).hasFDerivAt.sub ((d I).hasFDerivAt.const_mul I)).neg
  have E (u v : ℂ) : fderiv ℝ (dirPart v V) z u=fderiv ℝ (fderiv ℝ V) z u v :=
    (dirPart_inside u _ hz).symm.trans (dp2 h u v hz)
  have sym := ((h z hcl).contDiffAt (closedUpper_nhds hz)).isSymmSndFDerivAt (by simp) 1 I
  rw [dbar,(show HasFDerivAt (dirField V) _ z from hd).fderiv]
  simp only [dirLap,Pi.add_apply,dp2 h _ _ hz,ContinuousLinearMap.neg_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,E,sym]
  ring_nf <;> simp [Complex.I_sq] <;> ring

theorem dirPart_support (v : ℂ) (V : ℂ → ℂ) : tsupport (dirPart v V) ⊆ tsupport V := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx; by_contra hn
  have he : V=ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
  exact hx (by rw [dirPart,(he.filter_mono nhdsWithin_le_nhds).fderivWithin_eq he.eq_of_nhds, fderivWithin_zero]; rfl)

theorem closed_integrable_compact {V : ℂ → ℂ} (h : ContinuousOn V closedUpper) (hc : HasCompactSupport V) :
    Integrable V upperArea := by
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  have hcl : IsClosed closedUpper := isClosed_le continuous_const Complex.continuous_im
  have hs := hc.isCompact.inter_right hcl
  have hi : IntegrableOn V (tsupport V ∩ closedUpper) area := (h.mono (inter_subset_right (s:=tsupport V))).integrableOn_compact hs
  change IntegrableOn V upper area
  apply IntegrableOn.of_inter_support upper_open.measurableSet
  exact hi.mono_set (fun z hz => ⟨subset_tsupport V hz.2,(show 0<z.im from hz.1).le⟩)

end Liu
