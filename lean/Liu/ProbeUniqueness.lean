module

public import Liu.IntegrableReproducing
public import Liu.PolarizedDefect

@[expose] public section

noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate
namespace Liu

/-- Appendix A.1. The probes are (w-i)^m/(w+i)^(m+3), with the same
logarithmic growth condition as in the half-plane uniqueness lemma. -/
theorem halfPlane_probe_uniqueness {V : ℂ → ℂ} (hd : DifferentiableOn ℂ V upper)
    (hc : ContinuousOn V {w : ℂ | 0≤w.im}) {T K : ℝ} (hK : 0≤K)
    (hfar : ∀ w ∈ upper, T ≤ ‖w‖ → ‖V w‖ ≤ K*(1+log ‖w‖)/‖w‖)
    (hm : ∀ m : ℕ, ∫ w, V w*conj (uniquenessProbe m w) ∂upperArea = 0) :
    ∀ z ∈ upper, V z=0 := by
  apply uniqueness_of_probe_moments hd _ hm
  let f := fun w => V w*conj (bergmanKernel Complex.I w)
  let R := max 1 T
  let U := {w : ℂ | 0≤w.im}
  let core := closedBall (0:ℂ) R ∩ U
  have hU : IsClosed U := isClosed_le continuous_const Complex.continuous_im
  have hne (w : ℂ) (hw : w ∈ U) : w-conj Complex.I ≠ 0 := by
    have hh : 0≤w.im := hw
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he); simp at hi; linarith
  have hker : ContinuousOn (bergmanKernel Complex.I) U := by
    intro w hw
    unfold bergmanKernel
    fun_prop (disch := first | exact hne w hw | positivity | exact pow_ne_zero 2 (hne w hw))
  have hfc : ContinuousOn f U := by exact hc.mul (Complex.continuous_conj.comp_continuousOn hker)
  have hcore := (isCompact_closedBall (0:ℂ) R).inter_right hU
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  have hfi : IntegrableOn f core area := (hfc.mono inter_subset_right).integrableOn_compact hcore
  let tail := upper ∩ (closedBall (0:ℂ) R)ᶜ
  have hsub : tail ⊆ U := by intro w hw; exact (show 0<w.im from hw.1).le
  have htM : MeasurableSet tail := upper_open.measurableSet.inter Metric.isClosed_closedBall.measurableSet.compl
  let P := poleBound 1 (-Complex.I)
  have hbig : IntegrableOn (fun w => (2*K*P^2)*logTail w) tail area :=
    (show IntegrableOn _ upper area from logTail_integrable.const_mul (2*K*P^2)).mono_set inter_subset_left
  have htI : IntegrableOn f tail area := by
    apply hbig.mono' ((hfc.mono hsub).aestronglyMeasurable htM)
    filter_upwards [ae_restrict_mem (μ:=area) htM] with w hw
    have hr : R < ‖w‖ := by simpa using hw.2
    have h1 : 1≤‖w‖ := (le_max_left ..).trans hr.le
    have hp := zero_lt_one.trans_le h1
    have hW : 0<1+‖w‖ := by positivity
    have hk := pole_global_decay (a:=1) (w:=-Complex.I) (z:=w) (by norm_num) (by simp) (le_of_lt hw.1)
    have hker' : ‖bergmanKernel Complex.I w‖ ≤ (P/(1+‖w‖))^2 := by
      have hs := pow_le_pow_left₀ (norm_nonneg _) hk 2
      simpa [bergmanKernel,pole,P] using hs
    have hlog := log_le_log hp (show ‖w‖≤2+‖w‖ by linarith)
    have hV : ‖V w‖ ≤ (2*K)*(1+log (2+‖w‖))/(1+‖w‖) := by
      apply (hfar w hw.1 ((le_max_right ..).trans hr.le)).trans
      have hh : 1+log ‖w‖ ≤ 1+log (2+‖w‖) := by linarith
      have ha := mul_le_mul_of_nonneg_left hh hK
      have hnn := log_nonneg (show 1≤2+‖w‖ by linarith)
      apply (div_le_div_iff₀ hp hW).mpr
      nlinarith only [mul_le_mul_of_nonneg_right ha hW.le,
        mul_le_mul_of_nonneg_left (show 1+‖w‖≤2*‖w‖ by linarith) (by positivity : 0≤K*(1+log (2+‖w‖)))]
    rw [show f w = V w*conj (bergmanKernel Complex.I w) by rfl,norm_mul,Complex.norm_conj]
    have hnn := log_nonneg (show 1≤2+‖w‖ by linarith)
    apply (mul_le_mul hV hker' (norm_nonneg _) (by positivity)).trans_eq
    dsimp [logTail]; field_simp [hW.ne'] <;> ring
  exact (hfi.union htI).mono_set (by
    intro w hw
    by_cases h : w ∈ closedBall (0:ℂ) R
    · exact Or.inl ⟨h,(show 0<w.im from hw).le⟩
    · exact Or.inr ⟨hw,h⟩)

end Liu
