import Liu.LogTailKernel

noncomputable section
open Set Real Complex
open scoped ComplexConjugate
namespace Liu

/-- A lower-node downward ray meets an upper-partner upward ray exactly
when the node is directly above the partner, including coincidence. -/
def rayCollision (p q : ℂ) := p.re=q.re ∧ q.im ≤ p.im

theorem rayCollision_iff {p q : ℂ} : rayCollision p q ↔ ∃ t : ℝ, 0 ≤ t ∧ p-q=(t:ℂ)*I := by
  constructor
  · rintro ⟨h,h'⟩
    exact ⟨p.im-q.im,sub_nonneg.mpr h',by apply Complex.ext <;> simp [h]⟩
  · rintro ⟨t,ht,h⟩
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp at hr hi
    exact ⟨by linarith,by linarith⟩

def stripMass (s : ℂ) := (1+Complex.exp s)⁻¹

theorem stripMass_bounds {s : ℂ} (hs : |s.im| < π/2) : 0 < (stripMass s).re ∧ ‖stripMass s‖<1 := by
  have hc : 0 < Real.cos s.im := cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hs).1],(abs_lt.mp hs).2⟩
  have he : 0 < (Complex.exp s).re := by rw [Complex.exp_re]; exact mul_pos (exp_pos _) hc
  have hr : 1 < (1+Complex.exp s).re := by simp [he]
  have hn := hr.trans_le (re_le_norm _)
  constructor
  · unfold stripMass
    rw [Complex.inv_re]
    have nz : 1+Complex.exp s ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hn)
    exact div_pos (zero_lt_one.trans hr) (normSq_pos.mpr nz)
  · simpa [stripMass] using inv_lt_one_of_one_lt₀ hn

def windowLower (a : ℂ) (γ u : ℝ) : Fin 3 → ℂ :=
  ![-(u:ℂ)*I,-(u:ℂ)*I+direction γ,-(u:ℂ)*I+a*direction γ]

def windowUpper (a : ℂ) (γ u : ℝ) : Fin 3 → ℂ :=
  ![(u:ℂ)*I,(u:ℂ)*I+conj (direction γ),(u:ℂ)*I+a*conj (direction γ)]

theorem strip_no_collision {s : ℂ} (hs : |s.im| < π/2) {γ u : ℝ}
    (hg : γ∈Icc 0 (π/2)) (hu : 0 < u) (i j : Fin 3) :
    ¬rayCollision (windowLower (stripMass s) γ u i) (windowUpper (stripMass s) γ u j) := by
  let a := stripMass s
  let d := direction γ
  have S : 0 ≤ Real.sin γ := sin_nonneg_of_nonneg_of_le_pi hg.1 (by linarith [hg.2,pi_pos])
  have hd : d.im= -Real.sin γ := direction_im _
  have hm : ‖d‖=1 := direction_norm _
  have hdc : d*conj d=1 := by rw [Complex.mul_conj',hm]; norm_num
  obtain ⟨ha,hA⟩ := stripMass_bounds hs
  change 0 < a.re at ha
  change ‖a‖<1 at hA
  rw [rayCollision_iff]
  rintro ⟨t,ht,eq⟩
  let h := 2*u+t
  have hh : 0 < h := by dsimp [h]; linarith
  have hcast : (h:ℂ)=2*(u:ℂ)+(t:ℂ) := by dsimp [h]; push_cast; rfl
  have high (k : ℝ) (hk : 0 < k) : 1≤‖conj d+(k:ℂ)*I‖ ∧ 1≤‖d-(k:ℂ)*I‖ := by
    have hsq := Complex.sq_norm d
    rw [hm,Complex.normSq_apply,hd] at hsq
    constructor
    · have he := Complex.sq_norm (conj d+(k:ℂ)*I)
      simp [Complex.normSq_apply,hd] at he
      nlinarith [mul_nonneg hk.le S,norm_nonneg (conj d+(k:ℂ)*I)]
    · have he := Complex.sq_norm (d-(k:ℂ)*I)
      simp [Complex.normSq_apply,hd] at he
      nlinarith [mul_nonneg hk.le S,norm_nonneg (d-(k:ℂ)*I)]
  fin_cases i <;> fin_cases j
  all_goals change _ = (t:ℂ)*I at eq
  all_goals dsimp only [windowLower,windowUpper,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,
    Matrix.head_cons,Matrix.cons_val_fin_one] at eq
  all_goals try (have H := congrArg Complex.im eq; simp [direction_im] at H; linarith)
  · change -(u:ℂ)*I-((u:ℂ)*I+a*conj d)=(t:ℂ)*I at eq
    have e : a*conj d = -(h:ℂ)*I := by rw [hcast]; linear_combination -eq
    have e' := congrArg (fun z : ℂ => z*d) e
    change a*conj d*d= -(h:ℂ)*I*d at e'
    rw [mul_assoc,mul_comm (conj d),hdc,mul_one] at e'
    have hr := congrArg Complex.re e'
    simp [Complex.mul_re,Complex.mul_im,hd] at hr
    nlinarith [mul_nonneg hh.le S]
  · change -(u:ℂ)*I+d-((u:ℂ)*I+a*conj d)=(t:ℂ)*I at eq
    have e : a*conj d=d-(h:ℂ)*I := by rw [hcast]; linear_combination -eq
    have hr := congrArg norm e
    simp [norm_mul,hm] at hr
    linarith [(high h hh).2]
  · change -(u:ℂ)*I+a*d-(u:ℂ)*I=(t:ℂ)*I at eq
    have e : a*d=(h:ℂ)*I := by rw [hcast]; linear_combination eq
    have e' := congrArg (fun z : ℂ => z*conj d) e
    change a*d*conj d=(h:ℂ)*I*conj d at e'
    rw [mul_assoc,hdc,mul_one] at e'
    have hr := congrArg Complex.re e'
    simp [Complex.mul_re,Complex.mul_im,hd] at hr
    nlinarith [mul_nonneg hh.le S]
  · change -(u:ℂ)*I+a*d-((u:ℂ)*I+conj d)=(t:ℂ)*I at eq
    have e : a*d=conj d+(h:ℂ)*I := by rw [hcast]; linear_combination eq
    have hr := congrArg norm e
    simp [norm_mul,hm] at hr
    linarith [(high h hh).1]
  · change -(u:ℂ)*I+a*d-((u:ℂ)*I+a*conj d)=(t:ℂ)*I at eq
    have e : a*d-a*conj d=(h:ℂ)*I := by rw [hcast]; linear_combination eq
    have hi := congrArg Complex.im e
    simp [Complex.mul_im,hd] at hi
    nlinarith [mul_nonneg ha.le S]

end Liu
