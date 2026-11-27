module

public import Mathlib

@[expose] public section

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology
namespace Liu

/-- An integrable bound on each smaller parameter disc permits complex
differentiation under the integral. Schwarz bounds the difference quotients
without requiring an explicit majorant for parameter derivatives. -/
theorem differentiableOn_disc_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {F : ℂ → α → ℂ} (hm : ∀ w, AEStronglyMeasurable (F w) μ)
    (hd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => F w t) (ball 0 1))
    (hb : ∀ r : ℝ, 0<r → r<1 → ∃ M : α → ℝ, Integrable M μ ∧
      ∀ᵐ t ∂μ, ∀ w : ℂ, ‖w‖≤r → ‖F w t‖≤M t) :
    DifferentiableOn ℂ (fun w => ∫ t, F w t ∂μ) (ball 0 1) := by
  intro c hc
  have hc₁ : ‖c‖<1 := by simpa using hc
  let R := (1-‖c‖)/2
  have hR : 0<R := by dsimp [R]; linarith
  obtain ⟨M,hI,hM⟩ := hb (‖c‖+R) (by positivity) (by dsimp [R]; linarith)
  have hrad {w : ℂ} (hw : w∈ball c R) : ‖w‖≤‖c‖+R := by
    rw [mem_ball_iff_norm] at hw
    linarith [norm_sub_le_norm_sub_add_norm_sub w c 0,show ‖w‖≤‖w-c‖+‖c‖ by simpa using norm_sub_le_norm_sub_add_norm_sub w c 0]
  have hsub : ball c R⊆ball (0:ℂ) 1 := fun w hw => by
    rw [mem_ball_zero_iff]; have hh := hrad hw; dsimp [R] at hh; linarith
  have hi {w : ℂ} (hw : w∈ball c R) := hI.mono' (hm w) (hM.mono fun t h => h w (hrad hw))
  let Q := fun w t => slope (fun k => F k t) c w
  let D := fun t => deriv (fun k => F k t) c
  have hlim : Tendsto (fun w => ∫ t, Q w t ∂μ) (𝓝[≠] c) (𝓝 (∫ t, D t ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t => 2*M t/R)
    · apply Eventually.of_forall; intro w
      exact ((hm w).sub (hm c)).const_smul ((w-c)⁻¹)
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c hR),self_mem_nhdsWithin] with w hw hn
      have hne : w≠c := hn
      filter_upwards [hd,hM] with t ht htM
      have hmap : MapsTo (fun v => F v t) (ball c R) (closedBall (F c t) (2*M t)) := by
        intro v hv
        rw [mem_closedBall_iff_norm]
        linarith [norm_sub_le (F v t) (F c t),htM v (hrad hv),htM c (hrad (mem_ball_self hR))]
      simpa only [dslope_of_ne _ hne,Q] using Complex.norm_dslope_le_div_of_mapsTo_ball (ht.mono hsub) hmap hw
    · exact (hI.const_mul 2).div_const R
    · filter_upwards [hd] with t ht
      exact hasDerivAt_iff_tendsto_slope.mp (ht.differentiableAt (isOpen_ball.mem_nhds hc)).hasDerivAt
  apply DifferentiableAt.differentiableWithinAt
  apply HasDerivAt.differentiableAt (f':=∫ t, D t ∂μ)
  apply hasDerivAt_iff_tendsto_slope.mpr (hlim.congr' ?_)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c hR)] with w hw
  simp only [Q,slope_def_module,integral_smul,integral_sub (hi hw) (hi (mem_ball_self hR))]

end Liu
