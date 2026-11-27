module

public import Liu.LogTailKernel

@[expose] public section

noncomputable section
open Set Real Complex
namespace Liu

private theorem coefficient_norm (s : Bool) : ‖fieldCoefficient s‖=1/2 := by
  cases s <;> simp [fieldCoefficient,norm_div]

theorem tail_side_bounds (s : Bool) (P Q : Fin 3 → ℂ) (a b : ℂ) {X x C : ℝ}
    (hX : 10^18≤X) (hx : X≤|x|) (hp : ∀ i, 4*‖P i‖<X) (hq : ∀ j, 4*‖Q j‖<X)
    (hcost : sideLogCost s P Q ≤ C) :
    let U := Real.log (3*|x|/2)+π+C
    (∀ i, ‖tailSingle s P Q i (x:ℂ)‖ ≤ 2*U/|x|) ∧
      ‖tailCross s P Q a b (x:ℂ)‖ ≤ 4*(‖a‖+‖b‖)*U/|x| := by
  let U := Real.log (3*|x|/2)+π+C
  have H (i : Fin 2) (j : Fin 3) : ‖tailTerm s (P i.castSucc) (Q j) (x:ℂ)‖ ≤ 4*U/|x| :=
    tailTerm_bound hX hx (hp _) (hq _) ((constantLogCost_le s P Q i j).trans hcost)
  constructor
  · intro i
    rw [tailSingle,norm_mul,coefficient_norm]
    exact (mul_le_mul_of_nonneg_left (H i i.castSucc) (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring)
  · have B (i : Fin 2) (j k : Fin 3) :
        ‖tailTerm s (P i.castSucc) (Q j) (x:ℂ)-tailTerm s (P i.castSucc) (Q k) (x:ℂ)‖ ≤ 4*U/|x|+4*U/|x| :=
      (norm_sub_le ..).trans (add_le_add (H i j) (H i k))
    rw [tailCross,norm_mul,coefficient_norm]
    have hsum := add_le_add (mul_le_mul_of_nonneg_left (B 0 1 2) (norm_nonneg a))
      (mul_le_mul_of_nonneg_left (B 1 0 2) (norm_nonneg b))
    calc
      _ ≤ (1/2)*(‖a‖*(4*U/|x|+4*U/|x|)+‖b‖*(4*U/|x|+4*U/|x|)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply (norm_add_le ..).trans
        simpa only [norm_mul,Fin.castSucc_zero,show (1:Fin 2).castSucc=(1:Fin 3) by decide] using hsum
      _ = _ := by ring

private theorem tail_pair_bound {A B C D : ℂ} {K : ℝ} (hK : 0≤K)
    (ha : ‖A‖≤K) (hb : ‖B‖≤K) (hc : ‖C‖≤K) (hd : ‖D‖≤K) :
    ‖A*B+C*D‖ ≤ 2*K^2 := by
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_mul,two_mul,pow_two]
  exact add_le_add (mul_le_mul ha hb (norm_nonneg _) hK) (mul_le_mul hc hd (norm_nonneg _) hK)

/-- Lemma 6.7 on either real tail, for the explicit log branches used on
the moved and real contours and the full partner products at complex masses. -/
theorem subtracted_flux_tail_bound (P Q : Fin 3 → ℂ) (a b : ℂ) {X x : ℝ}
    (hX : 10^18≤X) (hP : ∀ i, 4*‖P i‖<X) (hQ : ∀ i, 4*‖Q i‖<X) (hx : X≤|x|) :
    ‖subtractedTail P Q a b (x:ℂ)‖ ≤
      ((8*‖a*b‖+32*(‖a‖+‖b‖)^2)*tailUpsilon P Q x^2+8*k₀*‖a*b‖)/x^2 := by
  let U := tailUpsilon P Q x
  let m := ‖a‖+‖b‖
  let V := 2*U/|x|
  let W := 4*m*U/|x|
  let G := 2/|x|
  have hp := tail_side_bounds true P Q a b hX hx hP hQ (le_add_of_nonneg_right (sideLogCost_nonneg false Q P))
  have hq := tail_side_bounds false Q P a b hX hx hQ hP (le_add_of_nonneg_left (sideLogCost_nonneg true P Q))
  let A := fun i => tailSingle true P Q i (x:ℂ)
  let B := fun i => tailSingle false Q P i (x:ℂ)
  let C := tailCross true P Q a b (x:ℂ)
  let D := tailCross false Q P a b (x:ℂ)
  let S := fun p => tailPole p (x:ℂ)
  have hA (i : Fin 2) : ‖A i‖≤V := hp.1 i
  have hB (i : Fin 2) : ‖B i‖≤V := hq.1 i
  have hC : ‖C‖≤W := hp.2
  have hD : ‖D‖≤W := hq.2
  have hx₀ : 0 < |x| := by linarith
  have hG : 0≤G := by dsimp [G]; positivity
  have hV : 0≤V := (norm_nonneg _).trans (hA 0)
  have hW : 0≤W := (norm_nonneg _).trans hD
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hk : 0≤k₀ := by unfold k₀; positivity
  have hS (p : ℂ) (h : 4*‖p‖<X) : ‖S p‖≤G := by
    rw [show ‖S p‖=‖(x:ℂ)-p‖⁻¹ by simp [S,tailPole]]
    simpa [G,div_eq_mul_inv,mul_comm] using inv_anti₀ (half_pos hx₀) (vertical_log_tail hX h hx).1
  have mixed (F : Fin 2 → ℂ) (hf : ∀ i, ‖F i‖≤V) : ‖a*F 0+b*F 1‖ ≤ m*V := by
    apply (norm_add_le ..).trans
    rw [norm_mul,norm_mul,show m*V=‖a‖*V+‖b‖*V by dsimp [m]; ring]
    exact add_le_add (mul_le_mul_of_nonneg_left (hf 0) (norm_nonneg a)) (mul_le_mul_of_nonneg_left (hf 1) (norm_nonneg b))
  have h₁ := tail_pair_bound hV (hA 0) (hB 1) (hA 1) (hB 0)
  have h₂ := tail_pair_bound hG (hS _ (hP 0)) (hS _ (hQ 1)) (hS _ (hP 1)) (hS _ (hQ 0))
  have expand : subtractedTail P Q a b x =
      (a*b)*(A 0*B 1+A 1*B 0)+(a*A 0+b*A 1)*D+C*(a*B 0+b*B 1)+C*D -
        ((k₀:ℂ)*(a*b))*(S (P 0)*S (Q 1)+S (P 1)*S (Q 0)) := by
    dsimp [subtractedTail,tailSide,A,B,C,D,S]; ring
  rw [expand]
  apply (norm_sub_le ..).trans
  have add4 (x y z t : ℂ) : ‖x+y+z+t‖≤‖x‖+‖y‖+‖z‖+‖t‖ :=
    by linarith [norm_add_le x y,norm_add_le (x+y) z,norm_add_le (x+y+z) t]
  apply (add_le_add (add4 ..) le_rfl).trans
  simp only [norm_mul,Complex.norm_of_nonneg hk]
  rw [←norm_mul a b]
  calc
    _ ≤ ‖a*b‖*(2*V^2)+(m*V)*W+W*(m*V)+W*W+(k₀*‖a*b‖)*(2*G^2) := by
      gcongr
      all_goals first | exact h₁ | exact h₂ | exact hC | exact hD | exact mixed A hA | exact mixed B hB | positivity
    _ = _ := by
      change _=((8*‖a*b‖+32*m^2)*U^2+8*k₀*‖a*b‖)/x^2
      rw [←sq_abs x]; dsimp only [V,W,G]; field_simp [hx₀.ne']; ring

theorem moved_flux_tail_bound (P Q : Fin 3 → ℂ) (a b : ℂ) (path : ℝ → ℂ) {X : ℝ}
    (hX : 10^18≤X) (hP : ∀ i, 4*‖P i‖<X) (hQ : ∀ i, 4*‖Q i‖<X)
    (hpath : ∀ x, X≤|x| → path x=(x:ℂ)) {x : ℝ} (hx : X≤|x|) :
    ‖subtractedTail P Q a b (path x)‖ ≤
      ((8*‖a*b‖+32*(‖a‖+‖b‖)^2)*tailUpsilon P Q x^2+8*k₀*‖a*b‖)/x^2 := by
  rw [hpath _ hx]
  exact subtracted_flux_tail_bound P Q a b hX hP hQ hx

end Liu
