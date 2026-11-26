import Liu.ChebyshevSeries

noncomputable section
open Real Set Polynomial Polynomial.Chebyshev
namespace Liu

theorem firstKind_eval_sum (n : ℕ) (f : ℂ → ℂ) (x : ℂ) :
    (firstKindInterpolant n f).eval x =
    ∑ j : Fin (n+1), f (firstKindNode n j)*(Lagrange.basis Finset.univ (firstKindNode n) j).eval x := by
  simp [firstKindInterpolant,Lagrange.interpolate_apply,eval_finsetSum]

private theorem tail_weight_sum {ρ M : ℝ} (hρ : 1<ρ) (n : ℕ) :
    HasSum (fun k : ℤ => if n<k.natAbs then 2*M/ρ^k.natAbs else 0)
      (4*M/(ρ^n*(ρ-1))) := by
  let g := fun k : ℕ => if n<k then 2*M/ρ^k else 0
  let A := 2*M/(ρ^n*(ρ-1))
  have hr := zero_lt_one.trans hρ
  have hgeo := hasSum_geometric_of_lt_one (inv_pos.mpr hr).le (inv_lt_one_of_one_lt₀ hρ)
  have htail : HasSum (fun k : ℕ => g (k+(n+1))) A := by
    convert hgeo.mul_left (2*M/ρ^(n+1)) using 1
    · funext k
      simp [g,show n<k+(n+1) by omega,pow_add,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
    · unfold A
      field_simp [hr.ne',show ρ-1≠0 by linarith,show 1-ρ⁻¹≠0 by linarith [inv_lt_one_of_one_lt₀ hρ]]
      ring
  have hz : ∑ k ∈ Finset.range (n+1), g k=0 := Finset.sum_eq_zero fun k hk => by
    simp [g,Nat.le_of_lt_succ (Finset.mem_range.mp hk)]
  have hg : HasSum g A := by simpa [hz] using (hasSum_nat_add_iff (n+1)).mp htail
  have hg1 : HasSum (fun k : ℕ => g (k+1)) A := by
    apply (hasSum_nat_add_iff 1).mpr
    simpa [g] using hg
  have h := HasSum.of_nat_of_neg_add_one (f:=fun k : ℤ => g k.natAbs)
    (by exact hg) (by
      convert hg1 using 1
      funext k; rw [Int.natAbs_neg]; rfl)
  convert h using 1
  dsimp [A]; ring

/-- Lemma 6.4 for the polynomial interpolant at the n+1 first-kind nodes;
the coefficient and alias bounds apply to every real point of the interval. -/
theorem firstKind_ellipse_error {χ : ℂ → ℂ} {ρ M : ℝ} (hρ : 1<ρ)
    (ha : AnalyticOnNhd ℂ χ (bernsteinEllipse ρ)) (hM : ∀ z∈bernsteinEllipse ρ, ‖χ z‖≤M)
    (n : ℕ) {x : ℝ} (hx : x∈Icc (-1:ℝ) 1) :
    ‖χ x-(firstKindInterpolant n χ).eval (x:ℂ)‖≤4*M/(ρ^n*(ρ-1)) := by
  obtain ⟨b,hb,hs⟩ := ellipse_cosine_series hρ ha hM
  let t := fun (k : ℤ) (z : ℂ) => (T ℂ k).eval z
  have hn (j : Fin (n+1)) := hs (Real.cos (firstKindAngle n j)) (show _∈Icc (-1:ℝ) 1 from ⟨neg_one_le_cos _,cos_le_one _⟩)
  have hm : HasSum (fun k : ℤ => b k*(firstKindInterpolant n (t k)).eval (x:ℂ))
      ((firstKindInterpolant n χ).eval (x:ℂ)) := by
    rw [firstKind_eval_sum]
    have h := hasSum_sum (s:=Finset.univ) (fun (j : Fin (n+1)) _ =>
      (hn j).mul_right ((Lagrange.basis Finset.univ (firstKindNode n) j).eval (x:ℂ)))
    convert h using 1 <;> first | rfl | skip
    funext k
    rw [firstKind_eval_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    change b k*(t k (firstKindNode n j)*_)=(b k*t k (firstKindNode n j))*_
    ring
  apply ((hs x hx).sub hm).norm_le_of_bounded (tail_weight_sum hρ n)
  intro k
  change ‖b k*t k x-b k*(firstKindInterpolant n (t k)).eval (x:ℂ)‖≤_
  by_cases hk : k.natAbs≤n
  · have hdeg : (T ℂ k).degree<(Finset.univ : Finset (Fin (n+1))).card := by
      rw [degree_T,Finset.card_univ,Fintype.card_fin]; exact_mod_cast Nat.lt_succ_of_le hk
    have he := Lagrange.eq_interpolate (firstKindNode_injective n).injOn hdeg
    simp only [firstKindInterpolant,t,←he,sub_self,norm_zero,if_neg (not_lt.mpr hk),le_refl]
  · rw [if_pos (lt_of_not_ge hk),←mul_sub,norm_mul]
    have e : T ℂ k=T ℂ (k.natAbs:ℤ) := by
      cases k with
      | ofNat m => rfl
      | negSucc m => exact T_neg ℂ ((m+1:ℕ):ℤ)
    have hI : ‖(firstKindInterpolant n (t k)).eval (x:ℂ)‖≤1 := by
      simpa only [t,e] using firstKind_interpolated_mode n k.natAbs hx
    have hT : ‖t k x‖≤1 := by
      change ‖(T ℂ k).eval (x:ℂ)‖≤1
      rw [←complex_ofReal_eval_T,Complex.norm_real,Real.norm_eq_abs]
      exact abs_eval_T_real_le_one k (abs_le.mpr hx)
    have hn' : ‖t k x-(firstKindInterpolant n (t k)).eval (x:ℂ)‖≤2 := by
      linarith [norm_sub_le (t k (x:ℂ)) ((firstKindInterpolant n (t k)).eval (x:ℂ))]
    apply (mul_le_mul (hb k) hn' (norm_nonneg _) ((norm_nonneg _).trans (hb k))).trans_eq
    ring

end Liu
