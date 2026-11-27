module

public import Liu.AngularExpansion

@[expose] public section

noncomputable section
open Set Filter Real
open scoped Topology
namespace Liu

private theorem homogeneous_dirichlet_unique {t : ℝ} (ht : 0<t) (ht1 : t<1) {h v : ℝ → ℂ}
    (h0 : h 0=0) (hπ : h π=0) (hd : ∀ x ∈ Icc 0 π,
      HasDerivWithinAt h (v x) (Icc 0 π) x ∧ HasDerivWithinAt v (-(t:ℂ)^2*h x) (Icc 0 π) x) :
    ∀ x ∈ Icc 0 π, h x=0 := by
  let W := fun a x : ℝ => v x*(sin (t*(x-a)):ℝ) - (t:ℂ)*h x*(cos (t*(x-a)):ℝ)
  have cons (a : ℝ) (ha : a ∈ Icc 0 π) : W a a=W a 0 := by
    have hdW (x : ℝ) (hx : x∈Icc 0 π) : HasDerivWithinAt (W a) 0 (Icc 0 π) x := by
      have dh := ((hasDerivAt_id x).sub_const a).const_mul t
      have hs := dh.sin.ofReal_comp.hasDerivWithinAt (s:=Icc 0 π)
      have hc := dh.cos.ofReal_comp.hasDerivWithinAt (s:=Icc 0 π)
      obtain ⟨dy,dv⟩ := hd x hx
      convert (dv.mul hs).sub ((dy.const_mul (t:ℂ)).mul hc) using 1
      · rfl
      · simp [id_eq]; ring
    have hc := (convex_Icc (0:ℝ) π).norm_image_sub_le_of_norm_hasDerivWithin_le hdW
      (C:=0) (fun _ _ => by simp) (left_mem_Icc.mpr pi_pos.le) ha
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hc))
  have iden (a : ℝ) (ha : a∈Icc 0 π) : (t:ℂ)*h a=v 0*(sin (t*a):ℝ) := by
    have e := cons a ha
    simpa [W,h0] using e
  have htC := Complex.ofReal_ne_zero.mpr ht.ne'
  have hs := sin_pos_of_pos_of_lt_pi (mul_pos ht pi_pos) (by nlinarith [mul_lt_mul_of_pos_right ht1 pi_pos])
  have hv : v 0=0 := by
    have he := iden π (right_mem_Icc.mpr pi_pos.le)
    rw [hπ,mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_right (Complex.ofReal_ne_zero.mpr hs.ne')
  intro a ha
  have he := iden a ha
  rw [hv,zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left htC

/-- The energy formula applies to the unique solution, including functions specified
only through derivatives within the closed angle interval. -/
theorem angularSolution_unique {t : ℝ} (ht : 0<t) (ht1 : t<1) {y v : ℝ → ℂ}
    (y0 : y 0=0) (yπ : y π=0) (h : ∀ x ∈ Icc 0 π, HasDerivWithinAt y (v x) (Icc 0 π) x ∧
      HasDerivWithinAt v (((1+t:ℝ):ℂ)*Complex.exp ((t:ℂ)*x*Complex.I)-(t:ℂ)^2*y x) (Icc 0 π) x) :
    EqOn y (fun x : ℝ => angularSolution t x) (Icc 0 π) := by
  obtain ⟨w,hw⟩ := angularSolution_real_system ht ht1
  obtain ⟨h0,hπ,_⟩ := angularSolution_dirichlet ht ht1
  let d := fun x : ℝ => y x-angularSolution t x
  have hd (x : ℝ) (hx : x∈Icc 0 π) : HasDerivWithinAt d (v x-w x) (Icc 0 π) x ∧
      HasDerivWithinAt (fun u => v u-w u) (-(t:ℂ)^2*d x) (Icc 0 π) x := by
    have h1 := h x hx
    have h2 := hw x
    refine ⟨h1.1.sub h2.1.hasDerivWithinAt,?_⟩
    convert h1.2.sub h2.2.hasDerivWithinAt using 1 <;> first | rfl | (dsimp only [d]; ring)
  have he := homogeneous_dirichlet_unique ht ht1 (h:=d) (v:=fun x => v x-w x)
    (by simp [d,y0,h0]) (by simp [d,yπ,hπ]) hd
  exact fun x hx => sub_eq_zero.mp (he x hx)

end Liu
