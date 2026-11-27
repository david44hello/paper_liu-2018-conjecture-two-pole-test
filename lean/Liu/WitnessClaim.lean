module

public import Liu.WitnessAsymptotic
public import Liu.WitnessEquality

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate
namespace Liu

theorem closure_upper_plane : closure upper={z : ℂ | 0≤z.im} := by
  have he : upper=(Set.univ: Set ℝ) ×ℂ Ioi 0 := by ext z; simp [upper,Complex.mem_reProdIm]
  rw [he,Complex.closure_reProdIm,closure_univ,closure_Ioi]
  ext z; simp [Complex.mem_reProdIm]

theorem PickSum.witness_identity {n : ℕ} (p : PickSum n) :
    isWitness (optimalWitness p.value) ∧ ∀ W : ℂ → ℂ, isWitness W →
      let g := witnessDifference p.value W
      let L := limUnder atTop (truncatedWitness p.value W)
      MemLp g 2 upperArea ∧ Tendsto (truncatedWitness p.value W) atTop (𝓝 (deficit p.value-energy g)) ∧
      L=deficit p.value-energy g ∧ L≤deficit p.value ∧
      (L=deficit p.value ↔ EqOn W (optimalWitness p.value) {z : ℂ | 0≤z.im}) := by
  have ho := p.optimalWitness_isWitness
  refine ⟨ho,?_⟩
  intro W hW
  dsimp only
  let g := witnessDifference p.value W
  let U := {z : ℂ | 0≤z.im}
  have hu : upper ⊆ U := fun z hz => (show 0<z.im from hz).le
  have hSc : ContinuousOn p.value U := fun z hz => (p.hasDerivAt hz).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g U := hSc.mul (hW.2.1.sub ho.2.1)
  have hgd : DifferentiableOn ℂ g upper := p.holomorphic.mul (hW.1.sub ho.1)
  obtain ⟨A,hA,R,hR,h₁⟩ := hW.2.2
  obtain ⟨B,hB,T,hT,h₂⟩ := ho.2.2
  let K := p.bound*(A+B)
  let R₀ := max 2 (max R T)
  have hK : 0≤K := by dsimp [K]; have := p.bound_pos; positivity
  have hdec (z : ℂ) (hz : 0≤z.im) (hr : R₀≤‖z‖) : ‖g z‖≤K*(1+log ‖z‖)/‖z‖^2 := by
    have hRz := (le_max_left R T).trans ((le_max_right 2 (max R T)).trans hr)
    have hTz := (le_max_right R T).trans ((le_max_right 2 (max R T)).trans hr)
    have h2z := (le_max_left 2 (max R T)).trans hr
    have hp : 0<‖z‖ := by linarith
    have hd := norm_sub_le_norm_sub_add_norm_sub (W z) ((π/2:ℝ):ℂ) (optimalWitness p.value z)
    rw [norm_sub_rev ((π/2:ℝ):ℂ)] at hd
    have hdiff := hd.trans (add_le_add (h₁ z hz hRz) (h₂ z hz hTz))
    have hs := (p.global_decay hz).trans (div_le_div_of_nonneg_left p.bound_pos.le hp (by linarith))
    change ‖p.value z*(W z-optimalWitness p.value z)‖ ≤ _
    rw [norm_mul]
    apply (mul_le_mul hs hdiff (norm_nonneg _) (by have := p.bound_pos; positivity)).trans_eq
    dsimp [K]; field_simp [hp.ne'] <;> ring
  obtain ⟨D,hD,hdom⟩ := log_square_tail_bound hgc hK hdec
  have hi := (integrable_one_add_norm (r:=3) (μ:=(volume:Measure ℂ)) (by norm_num)).const_mul (D^2)
  have hv : Integrable (fun w : ℂ => D^2*(1+‖w‖)^(-(3:ℝ))) upperArea :=
    (hi.smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).restrict
  have hgm : AEStronglyMeasurable g upperArea := hgd.continuousOn.aestronglyMeasurable upper_open.measurableSet
  have hG : MemLp g 2 upperArea := by
    apply (memLp_two_iff_integrable_sq_norm hgm).mpr
    apply hv.mono' (hgm.norm.pow 2)
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    apply (pow_le_pow_left₀ (norm_nonneg _) (hdom z (le_of_lt hz)) 2).trans_eq
    have hrp : 0<1+‖z‖ := by positivity
    rw [div_pow,←Real.rpow_natCast ((1+‖z‖)^(3/2:ℝ)) 2,←rpow_mul hrp.le,rpow_neg hrp.le]
    norm_num [div_eq_mul_inv]
  obtain ⟨hint,horth⟩ := p.field_orthogonality hgd hgc hK hdec
  have hl := witness_limit_of_orthogonality p W p.finite_part.1 hG hint horth
  obtain ⟨hlo,heq⟩ := witness_deficit_lower p W p.finite_part.1 hG hint horth
    (hW.2.1.mono hu) (ho.2.1.mono hu)
  refine ⟨hG,hl,hl.limUnder_eq,hlo,heq.trans ⟨?_,fun h => h.mono hu⟩⟩
  intro he
  have hcl : IsClosed U := isClosed_le continuous_const Complex.continuous_im
  have hcont := hcl.isClosed_eq hW.2.1 ho.2.1
  have hs : upper ⊆ {z ∈ U | W z=optimalWitness p.value z} := fun z hz => ⟨hu hz,he hz⟩
  have hx := closure_minimal hs hcont
  rw [closure_upper_plane] at hx
  exact fun z hz => (hx hz).2

end Liu
