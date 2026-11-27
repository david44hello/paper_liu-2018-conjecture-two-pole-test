module

public import Liu.OrthogonalBounds
public import Liu.RectangleGreen

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter
open scoped ComplexConjugate Topology
namespace Liu

/-- Orthogonality in Lemma 4.2, for every test allowed by the paper, including
ones with just continuous boundary values. -/
theorem PickSum.field_orthogonality {n : ℕ} (p : PickSum n) {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g upper) (hc : ContinuousOn g {z : ℂ | 0≤z.im})
    {T K : ℝ} (hK : 0≤K)
    (hg : ∀ z : ℂ, 0≤z.im → T≤‖z‖ → ‖g z‖ ≤ K*(1+log ‖z‖)/‖z‖^2) :
    Integrable (fun z => field p.value z*conj (g z)) upperArea ∧
      (∫ z, field p.value z*conj (g z) ∂upperArea)=0 := by
  obtain ⟨C,hC,hgc⟩ := log_square_tail_bound hc hK hg
  obtain ⟨B,hB,hv⟩ := p.field_decay
  obtain ⟨M,hM,hU⟩ := p.potential_bounded
  let v := field p.value
  let U := potential p.value
  let G := fun z => v z*conj (g z)
  have hvm := field_measurable p.value
  have hgm : AEStronglyMeasurable g upperArea := (hd.continuousOn.aestronglyMeasurable upper_open.measurableSet)
  have hmaj := (integrable_one_add_norm (μ:=(volume:Measure ℂ)) (r:=5/2) (by norm_num)).const_mul (B*C)
  have hInt : Integrable (fun w : ℂ => (B*C)*(1+‖w‖)^(-(5/2:ℝ))) upperArea :=
    (hmaj.smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).restrict
  have hG : Integrable G upperArea := by
    apply hInt.mono' (hvm.aestronglyMeasurable.mul (Complex.continuous_conj.comp_aestronglyMeasurable hgm))
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    change ‖G z‖ ≤ _
    rw [show ‖G z‖=‖v z‖*‖g z‖ by simp [G]]
    apply (mul_le_mul (hv z hz) (hgc z (le_of_lt hz)) (norm_nonneg _) (by positivity)).trans_eq
    let r := 1+‖z‖
    have hr : 0<r := by dsimp [r]; positivity
    change B/r*(C/r^(3/2:ℝ))=(B*C)*r^(-(5/2:ℝ))
    rw [rpow_neg hr.le,show (5/2:ℝ)=1+3/2 by norm_num,rpow_add hr,rpow_one,mul_inv_rev]; ring
  refine ⟨hG,?_⟩
  let H := fun z => conj (U z)*g z
  let k := fun z => -Complex.I * conj (G z)
  have hk : Integrable k upperArea := (Complex.conjCLE.toContinuousLinearMap.integrable_comp hG).const_mul _
  have hUc : ContinuousOn U {z : ℂ | 0≤z.im} := fun z hz => (p.potential_hasFDerivAt_closed hz).continuousAt.continuousWithinAt
  have hHc : ContinuousOn H {z : ℂ | 0≤z.im} := (Complex.continuous_conj.comp_continuousOn hUc).mul hc
  have dH (z : ℂ) (hz : z∈upper) := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z
    (p.potential_hasFDerivAt hz)).mul ((hd.differentiableAt (upper_open.mem_nhds hz)).hasDerivAt.complexToReal_fderiv)
  have hHd : DifferentiableOn ℝ H upper := fun z hz => (dH z hz).differentiableAt.differentiableWithinAt
  have hcurl (z : ℂ) (hz : z∈upper) : Complex.I*fderiv ℝ H z 1-fderiv ℝ H z Complex.I=k z := by
    have dz : HasFDerivAt H _ z := dH z hz
    rw [dz.fderiv]
    dsimp only [k,G,v,U,field]
    rw [(p.potential_hasFDerivAt hz).fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.one_apply,smul_eq_mul,ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply,
      Function.comp_apply,Pi.mul_apply,map_mul,map_sub,map_neg,Complex.conj_conj,Complex.conj_I,mul_one]
    ring_nf <;> simp [Complex.I_sq] <;> ring
  let b := fun R : ℝ => (M*C)/R^(3/2:ℝ)
  have hl : Tendsto (fun R => R*b R) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : 0<(1/2:ℝ))).const_mul (M*C)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    dsimp [b]
    rw [show (3/2:ℝ)=1+1/2 by norm_num,rpow_add hR,rpow_one,rpow_neg hR.le]
    field_simp [hR.ne',(rpow_pos_of_pos hR (1/2:ℝ)).ne'] <;> ring
  have dec : ∀ᶠ R in atTop, ∀ z : ℂ, 0≤z.im → R≤‖z‖ → ‖H z‖≤b R := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    intro z hz hRz
    rw [show ‖H z‖=‖U z‖*‖g z‖ by simp [H]]
    apply (mul_le_mul (hU z hz) (hgc z hz) (norm_nonneg _) hM).trans
    change M*(C/(1+‖z‖)^(3/2:ℝ)) ≤ (M*C)/R^(3/2:ℝ)
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hM
    exact div_le_div_of_nonneg_left hC (rpow_pos_of_pos hR _) (rpow_le_rpow hR.le (by linarith) (by norm_num))
  have hz := upper_curl_integral_zero hHc hHd hcurl (fun x => by simp [H,U,potential_boundary]) hk hl dec
  change (∫ w, -Complex.I*conj (G w) ∂upperArea) = 0 at hz
  rw [integral_const_mul,integral_conj,mul_eq_zero] at hz
  have he := hz.resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)
  exact (map_eq_zero (starRingEnd ℂ)).mp he

end Liu
