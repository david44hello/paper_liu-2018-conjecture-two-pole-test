import Liu.CanonicalRegularity
import Liu.HomogeneousGreen
import Liu.RectangleGreen

noncomputable section
open Set MeasureTheory Real Filter Metric
open scoped Topology ComplexConjugate
namespace Liu

/-- The pointwise decay hypothesis on the source in Appendix B, Lemma 1. -/
structure SupercriticalSource (f : ℂ → ℂ) (t : ℝ) : Prop where
  pos : 0 < t
  lt_one : t < 1
  measurable : Measurable f
  bound : ∃ K ≥ 0, ∀ w ∈ upper, ‖f w‖ ≤ K/(1+‖w‖)^(2+t)

theorem SupercriticalSource.green {f : ℂ → ℂ} {t : ℝ} (h : SupercriticalSource f t) :
    GreenSource f := by
  obtain ⟨K,hK,hs⟩ := h.bound
  exact GreenSource.of_decay (by linarith [h.pos] : 2<2+t) hK h.measurable hs

theorem GreenSource.quadratic {f : ℂ → ℂ} (h : GreenSource f) : QuadraticDecay f :=
  ⟨h.measurable,h.decay⟩

theorem SupercriticalSource.field_decay {f : ℂ → ℂ} {t : ℝ} (h : SupercriticalSource f t) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → ‖canonicalField f z‖ ≤ C/(1+‖z‖)^(1+t) := by
  obtain ⟨K,hK,hs⟩ := h.bound
  obtain ⟨A,hA,ha⟩ := greenResolvent_supercritical_decay h.pos h.lt_one hK hs
  let F := canonicalField f
  have hc : Continuous F := canonicalField_continuous h.green.quadratic
  have hw : Continuous (fun z : ℂ => ‖F z‖*(1+‖z‖)^(1+t)) := by
    apply hc.norm.mul
    have ht := h.pos
    fun_prop (disch := first | positivity | linarith)
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn hw.continuousOn
  refine ⟨|B|+A*(2:ℝ)^(1+t),by positivity,?_⟩
  intro z hz
  apply (le_div_iff₀ (rpow_pos_of_pos (by positivity) _)).mpr
  by_cases hr : ‖z‖≤1
  · have hb := hB z (by simpa using hr)
    change ‖‖F z‖*(1+‖z‖)^(1+t)‖≤B at hb
    exact ((le_abs_self _).trans hb).trans ((le_abs_self B).trans (le_add_of_nonneg_right (by positivity)))
  · have hp : 0<‖z‖ := zero_lt_one.trans (lt_of_not_ge hr)
    have ha' : ‖F z‖ ≤ A/‖z‖^(1+t) := by
      dsimp only [F]
      rw [canonicalField_eq_integral h.green.quadratic,norm_neg]
      exact (norm_integral_le_integral_norm _).trans (ha z hz (norm_pos_iff.mp hp))
    have hs' := rpow_le_rpow (by positivity : 0≤1+‖z‖) (by linarith [lt_of_not_ge hr] : 1+‖z‖≤2*‖z‖) (by linarith [h.pos] : 0≤1+t)
    rw [mul_rpow (by norm_num) hp.le] at hs'
    have hm := mul_le_mul ha' hs' (by positivity) (by positivity)
    change ‖F z‖*(1+‖z‖)^(1+t)≤_
    apply hm.trans
    rw [show A/‖z‖^(1+t)*((2:ℝ)^(1+t)*‖z‖^(1+t))=A*2^(1+t) by field_simp [(rpow_pos_of_pos hp (1+t)).ne']]
    exact le_add_of_nonneg_left (abs_nonneg _)

theorem memLp_two_of_power_bound {g : ℂ → ℂ} {t C : ℝ} (ht : 0<t) (hm : AEStronglyMeasurable g upperArea)
    (hb : ∀ z ∈ upper, ‖g z‖≤C/(1+‖z‖)^(1+t)) : MemLp g 2 upperArea := by
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hI := (integrable_one_add_norm (μ:=(volume:Measure ℂ)) (r:=(1+t)*2) (by simp; linarith [ht])).const_mul (C^2)
  have hU : Integrable (fun z : ℂ => C^2*(1+‖z‖)^(-((1+t)*2))) upperArea :=
    (hI.smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).restrict
  apply hU.mono' (by simpa only [pow_two,Pi.mul_def] using hm.norm.mul hm.norm)
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  apply (pow_le_pow_left₀ (norm_nonneg _) (hb z hz) 2).trans_eq
  rw [div_pow,rpow_neg (by positivity : 0≤1+‖z‖),rpow_mul (by positivity : 0≤1+‖z‖),rpow_ofNat,div_eq_mul_inv]

theorem SupercriticalSource.field_memLp {f : ℂ → ℂ} {t : ℝ} (h : SupercriticalSource f t) :
    MemLp (canonicalField f) 2 upperArea := by
  obtain ⟨C,_,hb⟩ := h.field_decay
  exact memLp_two_of_power_bound h.pos (canonicalField_continuous h.green.quadratic).aestronglyMeasurable
    (fun z hz => hb z (le_of_lt hz))

/-- Integration by parts for a bounded Dirichlet potential with a classical
differential in the interior, tested against a decaying field. -/
theorem dirichlet_field_pairing {U F g : ℂ → ℂ} {D : ℂ → ℂ →L[ℝ] ℂ}
    (hUc : ContinuousOn U {z : ℂ | 0≤z.im}) (dU : ∀ z ∈ upper, HasFDerivAt U (D z) z)
    (hF : ∀ z ∈ upper, F z= -(D z 1-Complex.I*D z Complex.I))
    (hbottom : ∀ x : ℝ, U x=0) {M : ℝ} (hM : 0≤M) (hU : ∀ z : ℂ, 0≤z.im → ‖U z‖≤M)
    (hc : ContinuousOn g {z : ℂ | 0≤z.im}) (hd : DifferentiableOn ℝ g upper)
    {s C : ℝ} (hs : 0<s) (hC : 0≤C)
    (hb : ∀ z : ℂ, 0≤z.im → ‖g z‖≤C/(1+‖z‖)^(1+s))
    (hi : Integrable (fun z => conj (F z)*g z) upperArea)
    (hj : Integrable (fun z => conj (U z)*dbar g z) upperArea) :
    (∫ z, conj (F z)*g z ∂upperArea) = 2*∫ z, conj (U z)*dbar g z ∂upperArea := by
  let H := fun z => conj (U z)*g z
  let k := fun z => -Complex.I*(conj (F z)*g z)+(2*Complex.I)*(conj (U z)*dbar g z)
  have dh (z : ℂ) (hz : z∈upper) := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z
    (dU z hz)).mul
    (hd.differentiableAt (upper_open.mem_nhds hz)).hasFDerivAt
  have hHd : DifferentiableOn ℝ H upper := fun z hz => (dh z hz).differentiableAt.differentiableWithinAt
  have hcurl (z : ℂ) (hz : z∈upper) : Complex.I*fderiv ℝ H z 1-fderiv ℝ H z Complex.I=k z := by
    have dz : HasFDerivAt H _ z := dh z hz
    rw [dz.fderiv]
    dsimp only [k,dbar]
    rw [hF z hz]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply,Function.comp_apply,smul_eq_mul,
      map_sub,map_mul,map_neg,Complex.conj_I]
    ring_nf <;> simp [Complex.I_sq] <;> ring
  have hHc : ContinuousOn H {z : ℂ | 0≤z.im} :=
    (Complex.continuous_conj.comp_continuousOn hUc).mul hc
  have hk : Integrable k upperArea := (hi.const_mul _).add (hj.const_mul _)
  let b := fun R : ℝ => (M*C)/R^(1+s)
  have hl : Tendsto (fun R => R*b R) atTop (𝓝 0) := by
    have he := (tendsto_rpow_neg_atTop hs).const_mul (M*C)
    simp only [mul_zero] at he
    apply he.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    dsimp only [b]
    rw [rpow_add hR,rpow_one,rpow_neg hR.le]
    field_simp [hR.ne',(rpow_pos_of_pos hR s).ne'] <;> ring
  have dec : ∀ᶠ R in atTop, ∀ z : ℂ, 0≤z.im → R≤‖z‖ → ‖H z‖≤b R := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    intro z hz hr
    have hu := hU z hz
    rw [show ‖H z‖=‖U z‖*‖g z‖ by simp [H]]
    apply (mul_le_mul hu (hb z hz) (norm_nonneg _) hM).trans
    dsimp only [b]; rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hC (rpow_pos_of_pos hR _)
      (rpow_le_rpow hR.le (by linarith) (by linarith))) hM
  have hzero := upper_curl_integral_zero hHc hHd hcurl (fun x => by simp [H,hbottom]) hk hl dec
  dsimp only [k] at hzero
  rw [integral_add (hi.const_mul _) (hj.const_mul _),integral_const_mul,integral_const_mul] at hzero
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination -hzero

/-- Green's first-order integration-by-parts identity in normalized area.
The test may have a nonzero antiholomorphic derivative. -/
theorem GreenSource.field_pairing {f g : ℂ → ℂ} (h : GreenSource f)
    (hc : ContinuousOn g {z : ℂ | 0≤z.im}) (hd : DifferentiableOn ℝ g upper)
    {s C : ℝ} (hs : 0<s) (hC : 0≤C)
    (hb : ∀ z : ℂ, 0≤z.im → ‖g z‖≤C/(1+‖z‖)^(1+s))
    (hi : Integrable (fun z => conj (canonicalField f z)*g z) upperArea)
    (hj : Integrable (fun z => conj (reflectedPotential f z)*dbar g z) upperArea) :
    (∫ z, conj (canonicalField f z)*g z ∂upperArea) =
      2*∫ z, conj (reflectedPotential f z)*dbar g z ∂upperArea := by
  obtain ⟨K,hK,hq⟩ := h.decay
  obtain ⟨M,hM,hU⟩ := green_L1_bound h.integrable h.measurable hK hq
  have hiU (z : ℂ) (hz : z∈upper) := (hU z (le_of_lt hz)).1
  exact dirichlet_field_pairing (reflectedPotential_continuous_closed h.quadratic hiU)
    (fun _ hz => reflectedPotential_hasFDerivAt h.measurable hK hq hiU hz)
    (fun _ hz => canonicalField_from_differential h.quadratic (le_of_lt hz))
    (reflectedPotential_boundary f) hM (fun z hz => (norm_integral_le_integral_norm _).trans (hU z hz).2)
    hc hd hs hC hb hi hj

end Liu
