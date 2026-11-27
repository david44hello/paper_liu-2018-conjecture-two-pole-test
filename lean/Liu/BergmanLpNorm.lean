module

public import Liu.ProjectionKernel
public import Liu.LiuGammaPower

@[expose] public section

noncomputable section
open Set MeasureTheory Real Complex
open scoped ENNReal Topology
namespace Liu

/-- The sharp Lp norm of the half-plane integral operator, written in the
extended nonnegative reals so the definition also permits an unbounded operator. -/
def bergmanLpNorm (p : ℝ) : ℝ≥0∞ :=
  ⨆ (f : ℂ → ℂ) (_ : MemLp f (ENNReal.ofReal p) upperArea)
    (_ : eLpNorm f (ENNReal.ofReal p) upperArea≠0),
    eLpNorm (bergmanIntegral f) (ENNReal.ofReal p) upperArea/eLpNorm f (ENNReal.ofReal p) upperArea

private theorem bergmanIntegral_ae_zero {f : ℂ → ℂ} (hf : f=ᵐ[upperArea] 0) : bergmanIntegral f=0 := by
  funext z
  change (∫ w, f w*starRingEnd ℂ (bergmanKernel z w) ∂upperArea)=0
  apply integral_eq_zero_of_ae
  filter_upwards [hf] with w hw
  simp [hw]

theorem bergmanLpNorm_le_iff {p : ℝ} (hp : 0<p) {M : ℝ≥0∞} :
    bergmanLpNorm p≤M ↔ ∀ f : ℂ → ℂ, MemLp f (ENNReal.ofReal p) upperArea →
      eLpNorm (bergmanIntegral f) (ENNReal.ofReal p) upperArea≤M*eLpNorm f (ENNReal.ofReal p) upperArea := by
  simp only [bergmanLpNorm,iSup_le_iff]
  constructor
  · intro h f hf
    by_cases hz : eLpNorm f (ENNReal.ofReal p) upperArea=0
    · rw [bergmanIntegral_ae_zero ((eLpNorm_eq_zero_iff (by simpa using hp)).mp hz)]
      simp
    · exact (ENNReal.div_le_iff_le_mul (.inl hz) (.inl hf.eLpNorm_lt_top.ne)).mp (h f hf hz)
  · intro h f hf hz
    exact (ENNReal.div_le_iff_le_mul (.inl hz) (.inl hf.eLpNorm_lt_top.ne)).mpr (h f hf)

/-- For every bounded realization with the integral kernel, the sharp
Lp majorant is equivalent to the ordinary continuous-linear-map norm bound. -/
theorem bergmanLpNorm_operator_bound_iff {p M : ℝ} (hp : 1≤p) (hM : 0≤M)
    [Fact (1≤ENNReal.ofReal p)]
    (B : Lp ℂ (ENNReal.ofReal p) upperArea →L[ℂ] Lp ℂ (ENNReal.ofReal p) upperArea)
    (hB : ∀ (f : ℂ → ℂ) (hf : MemLp f (ENNReal.ofReal p) upperArea),
      ⇑(B (hf.toLp f))=ᵐ[upperArea] bergmanIntegral f) :
    bergmanLpNorm p≤ENNReal.ofReal M ↔ ‖B‖≤M := by
  rw [bergmanLpNorm_le_iff (by linarith : 0<p),ContinuousLinearMap.opNorm_le_iff hM]
  have eq (f : ℂ → ℂ) (hf : MemLp f (ENNReal.ofReal p) upperArea) :
      eLpNorm (bergmanIntegral f) (ENNReal.ofReal p) upperArea =
        ENNReal.ofReal ‖B (hf.toLp f)‖ := by
    rw [←eLpNorm_congr_ae (hB f hf),ofReal_norm,Lp.enorm_def]
  have E (f : ℂ → ℂ) (hf : MemLp f (ENNReal.ofReal p) upperArea) :
      eLpNorm (bergmanIntegral f) (ENNReal.ofReal p) upperArea ≤ ENNReal.ofReal M * eLpNorm f (ENNReal.ofReal p) upperArea ↔
        ‖B (hf.toLp f)‖≤M*‖hf.toLp f‖ := by
    rw [eq f hf,←Lp.enorm_toLp hf,←ofReal_norm,←ENNReal.ofReal_mul hM,ENNReal.ofReal_le_ofReal_iff (by positivity)]
  constructor
  · intro h x
    simpa only [Lp.toLp_coeFn] using (E x (Lp.memLp x)).mp (h x (Lp.memLp x))
  · intro h f hf
    exact (E f hf).mpr (h _)

theorem bergmanLpNorm_power_bound {p : ℝ} (hp : 1<p) (h : bergmanLpNorm p≤ENNReal.ofReal (liuNorm p))
    {F f : ℂ → ℂ} (hf : MemLp f (ENNReal.ofReal p) upperArea)
    (hF : MemLp F (ENNReal.ofReal p) upperArea) (heq : bergmanIntegral f=ᵐ[upperArea] F) :
    (∫ z, ‖F z‖^p ∂upperArea) ≤ (liuNorm p)^p*(∫ z, ‖f z‖^p ∂upperArea) := by
  have hp₀ : 0<p := by linarith
  have h₀ : ENNReal.ofReal p≠0 := by simpa using hp₀
  have hpos := liuNorm_pos hp
  have H := (bergmanLpNorm_le_iff hp₀).mp h f hf
  rw [eLpNorm_congr_ae heq,hF.eLpNorm_eq_integral_rpow_norm h₀ ENNReal.ofReal_ne_top,
    hf.eLpNorm_eq_integral_rpow_norm h₀ ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hp₀.le,
    ←ENNReal.ofReal_mul hpos.le] at H
  have nonneg (g : ℂ → ℂ) : 0≤∫ z, ‖g z‖^p ∂upperArea := integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hf₀ := nonneg f
  have hF₀ := nonneg F
  have H' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp H
  have H'' := Real.rpow_le_rpow (Real.rpow_nonneg hF₀ _) H' hp₀.le
  rwa [Real.mul_rpow hpos.le (Real.rpow_nonneg hf₀ _),←Real.rpow_mul hf₀,←Real.rpow_mul hF₀,
    inv_mul_cancel₀ hp₀.ne',Real.rpow_one,Real.rpow_one] at H''

end Liu
