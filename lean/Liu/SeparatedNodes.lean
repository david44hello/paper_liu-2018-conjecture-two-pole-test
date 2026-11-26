import Liu.ReciprocalTrace

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate

/-- A one-complex-parameter family of unit-total-mass two-pole functions.
The continued upper partners at w are the conjugates of the nodes at conj w. -/
structure Liu.PickChart where
  mass : ℂ → ℂ
  left : ℂ → ℂ
  right : ℂ → ℂ

namespace Liu.PickChart

def zeroNode (P : PickChart) (w : ℂ) : ℂ :=
  P.mass w * P.right w + (1-P.mass w) * P.left w

structure Regular (P : PickChart) (U : Set ℂ) : Prop where
  isOpen : IsOpen U
  reflection : ∀ w ∈ U, conj w ∈ U
  mass : DifferentiableOn ℂ P.mass U
  left : DifferentiableOn ℂ P.left U
  right : DifferentiableOn ℂ P.right U
  left_below : ∀ w ∈ U, (P.left w).im < 0
  right_below : ∀ w ∈ U, (P.right w).im < 0
  zero_below : ∀ w ∈ U, (P.zeroNode w).im < 0

def nodeFactor (p z : ℂ) : ℂ := (z-p)/(z+Complex.I)

def nodeWeight (p : ℂ) : ℝ := max (1+‖p+Complex.I‖) (poleBound 1 p)

theorem nodeFactor_bounds {p z : ℂ} (hp : p.im<0) (hz : 0≤z.im) :
    nodeFactor p z ≠ 0 ∧ ‖nodeFactor p z‖ ≤ nodeWeight p ∧
    ‖(nodeFactor p z)⁻¹‖ ≤ nodeWeight p := by
  have hZ : 1≤‖z+Complex.I‖ := (show 1≤(z+Complex.I).im by simp; linarith).trans (Complex.im_le_norm _)
  have hpos := lt_of_lt_of_le zero_lt_one hZ
  have hn : z-p ≠ 0 := sub_ne_zero.mpr fun he => by rw [he] at hz; linarith
  refine ⟨div_ne_zero hn (norm_pos_iff.mp hpos),?_,?_⟩
  · apply le_max_of_le_left
    rw [nodeFactor,norm_div,div_le_iff₀ hpos]
    have h := norm_sub_le (z+Complex.I) (p+Complex.I)
    rw [add_sub_add_right_eq_sub] at h
    nlinarith [mul_le_mul_of_nonneg_left hZ (norm_nonneg (p+Complex.I))]
  · apply le_max_of_le_right
    have h := pole_global_decay (a:=1) zero_lt_one hp hz
    simp only [pole,Complex.ofReal_one,norm_div,norm_neg,norm_one] at h
    have h' := (div_le_div_iff₀ (norm_pos_iff.mpr hn) (by positivity : 0<1+‖z‖)).mp h
    have hn' := norm_pos_iff.mpr hn
    rw [nodeFactor,inv_div,norm_div,div_le_iff₀ hn']
    exact (norm_add_le ..).trans (by simpa [add_comm] using h')

def size (P : PickChart) (w : ℂ) : ℝ :=
  max 1 (max ‖P.mass w‖ (max ‖1-P.mass w‖
    (max (nodeWeight (P.left w)) (max (nodeWeight (P.right w)) (nodeWeight (P.zeroNode w))))))

def valueFactor (P : PickChart) (w z : ℂ) : ℂ :=
  nodeFactor (P.zeroNode w) z * (nodeFactor (P.left w) z)⁻¹ * (nodeFactor (P.right w) z)⁻¹

/-- The logarithmic derivative factor paired with the value factor in the area source. -/
def derivativeRatio (P : PickChart) (w z : ℂ) : ℂ :=
  let A := nodeFactor (P.left w) z
  let B := nodeFactor (P.right w) z
  let N := nodeFactor (P.zeroNode w) z
  P.mass w * A⁻¹ * B * N⁻¹ + (1-P.mass w) * B⁻¹ * A * N⁻¹

theorem factors_bounded {P : PickChart} {U : Set ℂ} (h : P.Regular U) {w : ℂ} (hw : w∈U)
    {z : ℂ} (hz : 0≤z.im) :
    ‖P.valueFactor w z‖ ≤ (P.size w)^3 ∧ ‖P.derivativeRatio w z‖ ≤ 2*(P.size w)^4 := by
  have L := nodeFactor_bounds (h.left_below w hw) hz
  have R := nodeFactor_bounds (h.right_below w hw) hz
  have N := nodeFactor_bounds (h.zero_below w hw) hz
  have bL : nodeWeight (P.left w) ≤ P.size w := by simp [size,le_max_iff]
  have bR : nodeWeight (P.right w) ≤ P.size w := by simp [size,le_max_iff]
  have bN : nodeWeight (P.zeroNode w) ≤ P.size w := by simp [size,le_max_iff]
  have ba : ‖P.mass w‖ ≤ P.size w := by simp [size,le_max_iff]
  have bb : ‖1-P.mass w‖ ≤ P.size w := by simp [size,le_max_iff]
  have hK : 0 ≤ P.size w := (norm_nonneg _).trans ba
  have b₁ := L.2.1.trans bL
  have b₂ := L.2.2.trans bL
  have b₃ := R.2.1.trans bR
  have b₄ := R.2.2.trans bR
  have b₅ := N.2.1.trans bN
  have b₆ := N.2.2.trans bN
  constructor
  · simp only [valueFactor,norm_mul,pow_succ,pow_zero,one_mul]
    gcongr
  · unfold derivativeRatio
    apply (norm_add_le ..).trans
    simp only [norm_mul]
    rw [two_mul]
    simp only [pow_succ,pow_zero,one_mul]
    gcongr

theorem Regular.zero_diff {P : PickChart} {U : Set ℂ} (h : P.Regular U) :
    DifferentiableOn ℂ P.zeroNode U :=
  (h.mass.mul h.right).add ((h.mass.const_sub 1).mul h.left)

theorem Regular.size_continuous {P : PickChart} {U : Set ℂ} (h : P.Regular U) {w : ℂ} (hw : w∈U) :
    ContinuousAt P.size w := by
  have hm := (h.mass.differentiableAt (h.isOpen.mem_nhds hw)).continuousAt
  have hl := (h.left.differentiableAt (h.isOpen.mem_nhds hw)).continuousAt
  have hr := (h.right.differentiableAt (h.isOpen.mem_nhds hw)).continuousAt
  have ho := (h.zero_diff.differentiableAt (h.isOpen.mem_nhds hw)).continuousAt
  have hn (f : ℂ → ℂ) (hf : ContinuousAt f w) (ht : (f w).im < 0) :
      ContinuousAt (fun v => nodeWeight (f v)) w := by
    have hn' : -(f w).im ≠ 0 := neg_ne_zero.mpr ht.ne
    unfold nodeWeight poleBound
    fun_prop (disch := assumption)
  exact continuousAt_const.max (hm.norm.max ((continuousAt_const.sub hm).norm.max
    ((hn _ hl (h.left_below w hw)).max ((hn _ hr (h.right_below w hw)).max (hn _ ho (h.zero_below w hw))))))

end Liu.PickChart
