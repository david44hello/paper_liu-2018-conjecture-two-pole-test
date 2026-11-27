module

public import Liu.GreenBoundary

@[expose] public section

noncomputable section
open Set MeasureTheory Filter Real
open scoped ComplexConjugate Topology
namespace Liu

def translatedTrace (ρ : ℂ → ℂ) (z v : ℂ) : ℂ :=
  if 0 < (z+v).im then ((greenLog z (z+v)/z.im:ℝ):ℂ)*ρ (z+v) else 0

def boundaryTraceIntegrand (ρ : ℂ → ℂ) (x : ℝ) (v : ℂ) : ℂ :=
  if 0 < v.im then ((2*v.im/‖v‖^2:ℝ):ℂ)*ρ ((x:ℂ)+v) else 0

/-- The kernel divided by height after translating the integration coordinate
so its singularity stays at v=0 as the evaluation point moves. -/
theorem greenLog_translated_ratio {z v : ℂ} (hz : 0 < z.im) (hw : 0 < (z+v).im)
    (hv : v ≠ 0) :
    greenLog z (z+v)/z.im = ((1/2:ℝ)*log (1+4*z.im*(z.im+v.im)/‖v‖^2))/z.im := by
  have hn : z ≠ z+v := by simpa using hv
  rw [greenLog_ratio_squared z (z+v) hz.le hw hn]
  simp

private theorem log_ratio_limit (v : ℂ) (hv : v ≠ 0) :
    Tendsto (fun y : ℝ => ((1/2:ℝ)*log (1+4*y*(y+v.im)/‖v‖^2))/y)
      (𝓝[>] 0) (𝓝 (2*v.im/‖v‖^2)) := by
  let D := ‖v‖^2
  have hi := hasDerivAt_id (0:ℝ)
  have d₁ := ((((hi.const_mul 4).mul (hi.add_const v.im)).div_const D).const_add 1)
  have d₂ := (d₁.log (by simp)).const_mul (1/2:ℝ)
  have H := d₂.tendsto_slope_zero_right
  convert H using 1 <;> simp [D,smul_eq_mul,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] <;> ring_nf <;> simp

theorem translatedTrace_limit {ρ : ℂ → ℂ} (x : ℝ)
    (hc : ContinuousOn ρ {w : ℂ | 0 ≤ w.im}) (v : ℂ) :
    Tendsto (fun z => translatedTrace ρ z v) (𝓝[upper] (x:ℂ))
      (𝓝 (boundaryTraceIntegrand ρ x v)) := by
  have hid : Tendsto (fun z : ℂ => z) (𝓝[upper] (x:ℂ)) (𝓝 (x:ℂ)) := nhdsWithin_le_nhds
  have hi : Tendsto Complex.im (𝓝[upper] (x:ℂ)) (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_im.continuousAt.tendsto.comp hid
  have hp : ∀ᶠ z in 𝓝[upper] (x:ℂ), z ∈ upper := self_mem_nhdsWithin
  by_cases negv : v.im < 0
  · have he := hi.eventually_lt_const (show 0 < -v.im by linarith)
    have eqn : ∀ᶠ z in 𝓝[upper] (x:ℂ), translatedTrace ρ z v = 0 := by
      filter_upwards [he] with z hz
      change z.im < -v.im at hz
      simp [translatedTrace,show ¬0 < z.im+v.im by linarith]
    simpa [boundaryTraceIntegrand,not_lt.mpr negv.le] using (tendsto_const_nhds (x:= (0:ℂ))).congr' (eqn.mono fun _ h => h.symm)
  by_cases hv : v = 0
  · subst v
    simpa [translatedTrace,boundaryTraceIntegrand,greenLog] using (tendsto_const_nhds (x:=(0:ℂ)) (f:=𝓝[upper] (x:ℂ)))
  have hv0 := le_of_not_gt negv
  have hzv : ∀ᶠ z in 𝓝[upper] (x:ℂ), 0 < (z+v).im := hp.mono
    (fun z hz => by simpa using add_pos_of_pos_of_nonneg (show 0<z.im from hz) hv0)
  have hi' : Tendsto Complex.im (𝓝[upper] (x:ℂ)) (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hi,hp⟩
  have hk := (log_ratio_limit v hv).comp hi'
  have hadd : Tendsto (fun z : ℂ => z+v) (𝓝[upper] (x:ℂ))
      (𝓝[{w : ℂ | 0 ≤ w.im}] ((x:ℂ)+v)) := tendsto_nhdsWithin_iff.mpr
    ⟨hid.add_const v,hzv.mono fun _ h => h.le⟩
  have hr := (hc _ (show (x:ℂ)+v ∈ {w : ℂ | 0 ≤ w.im} from by simpa using hv0)).tendsto.comp hadd
  have hprod := (Complex.continuous_ofReal.continuousAt.tendsto.comp hk).mul hr
  have hh : boundaryTraceIntegrand ρ x v = ((2*v.im/‖v‖^2:ℝ):ℂ)*ρ ((x:ℂ)+v) := by
    by_cases hvpos : 0 < v.im
    · simp [boundaryTraceIntegrand,hvpos]
    · have heq : v.im = 0 := le_antisymm (le_of_not_gt hvpos) hv0
      simp [boundaryTraceIntegrand,heq]
  rw [hh]
  apply hprod.congr'
  filter_upwards [hp,hzv] with z hz hzw
  simp only [translatedTrace,if_pos hzw,greenLog_translated_ratio hz hzw hv,Function.comp_apply]

theorem translatedTrace_measurable {ρ : ℂ → ℂ} (hρ : Measurable ρ) (z : ℂ) :
    Measurable (translatedTrace ρ z) := by
  unfold translatedTrace greenLog
  apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop) measurable_const

end Liu
