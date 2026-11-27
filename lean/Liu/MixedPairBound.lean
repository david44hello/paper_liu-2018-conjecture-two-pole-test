module

public import Liu.MixedTrace

@[expose] public section

noncomputable section
open Set Real MeasureTheory
namespace Liu

/-- After subtracting the Poisson cutoff times the limiting value at the
shallow foot, the singular trace has a uniformly integrable remainder. -/
theorem mixed_pair_majorant {s γ u x : ℝ} (hg : γ∈Icc 0 (π/2)) (hσ : 0<sin γ)
    (hu : 0<u) (hu₁ : u≤1/4) (hx : x≠0) :
    let a := normalMass s
    let C := 8/(a*sin γ^4)
    let H := mixedTrace s γ u x
    let star := mixedTrace s γ 0 0
    let P := poissonLine 0 1 x
    let I := isolatedTrace 0 u x
    let L := 1+log (1/u)
    |2*a*I*(H-star*P)| ≤ 132*C*P + H^2/C + 20*C*u*L*cutTrace 0 u x + 40*C*edgeLogWeight x := by
  let a := normalMass s
  let C := 8/(a*sin γ^4)
  let H := mixedTrace s γ u x
  let B := mixedTrace s γ 0 x
  let star := mixedTrace s γ 0 0
  let P := poissonLine 0 1 x
  let I := isolatedTrace 0 u x
  let L := 1+log (1/u)
  have ha : 0<a := Certificate.normalMass_pos _
  have ha₁ : a≤1 := by dsimp [a]; linarith [Certificate.complement_normalMass s,Certificate.normalMass_pos (-s)]
  obtain ⟨hC8,hsup,hspace,hdepth,_⟩ := mixed_trace_controls (s:=s) hg hσ
  change 8≤C at hC8
  have hC : 0<C := by linarith
  have hH : |H|≤4*C := hsup u hu.le x
  have hstar : |star|≤4*C := hsup 0 le_rfl 0
  have hP : 0<P := by dsimp [P,poissonLine]; positivity
  have hI : 0≤I := isolatedTrace_nonneg _ _ hu
  have hx₀ := abs_pos.mpr hx
  have hL : 0≤L := by dsimp [L]; linarith [log_nonneg ((one_le_div hu).mpr (by linarith : u≤1))]
  have hW := edgeLogWeight_nonneg x
  have hcut : cutTrace 0 u x = P*I := rfl
  have hD : I≤2/|x| := by
    apply (isolatedTrace_le_distance 0 x hu hx).trans
    rw [sub_zero,div_le_div_iff₀ (by positivity) hx₀]
    nlinarith only [mul_le_mul_of_nonneg_right pi_lt_four.le hx₀.le]
  have hIx := (le_div_iff₀ hx₀).mp hD
  have hPr : P=1/(1+x^2) := by dsimp [P,poissonLine]; ring
  change |2*a*I*(H-star*P)|≤132*C*P+H^2/C+20*C*u*L*cutTrace 0 u x+40*C*edgeLogWeight x
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*a*I),hcut]
  have haI : 2*a*I≤2*I := by nlinarith only [mul_le_mul_of_nonneg_right ha₁ hI]
  apply (mul_le_mul_of_nonneg_right haI (abs_nonneg _)).trans
  by_cases hn : |x|≤1/4
  · have hx₁ : |x|≤1 := by linarith
    have hP₁ : 1≤2*P := by
      rw [hPr,mul_one_div,le_div_iff₀ (by positivity)]
      nlinarith only [sq_abs x,pow_le_pow_left₀ hx₀.le hx₁ 2]
    have hIP : I≤2*(P*I) := by nlinarith only [mul_le_mul_of_nonneg_right hP₁ hI]
    have hsub : 1-P=x^2*P := by rw [hPr]; field_simp [show 1+x^2 ≠ 0 by positivity]; ring
    have hs : |star-star*P|≤4*C*x^2*P := by
      rw [show star-star*P=star*(1-P) by ring,hsub,abs_mul,abs_of_nonneg (by positivity : 0≤x^2*P)]
      nlinarith only [mul_le_mul_of_nonneg_right hstar (by positivity : 0≤x^2*P)]
    have hd : |H-B|≤5*C*u*L := hdepth u hu hu₁ x
    have hsp : |B-star|≤5*C*|x| *(1+log (1/|x|)) := hspace x hx₀ hn
    have htri : |H-star*P|≤5*C*u*L+5*C*|x| *(1+log (1/|x|))+4*C*x^2*P := by
      rw [show H-star*P=(H-B)+(B-star)+(star-star*P) by ring]
      exact (abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add hd hsp)) hs)
    have hlog := edge_log_sqrt_bound hx₀
    rw [div_eq_mul_inv 2,←edgeLogWeight_value hx₀ hx₁] at hlog
    have hlog₀ : 0≤1+log (1/|x|) := by linarith [log_nonneg ((one_le_div hx₀).mpr hx₁)]
    have hspace' : I*(5*C*|x| *(1+log (1/|x|)))≤20*C*edgeLogWeight x := by
      nlinarith only [mul_le_mul_of_nonneg_right hIx (mul_nonneg hC.le hlog₀),
        mul_le_mul_of_nonneg_left hlog hC.le]
    have hxx : I*x^2≤2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hIx hx₀.le,hx₁,congrArg (fun t : ℝ => I*t) (sq_abs x)]
    have hrest := mul_le_mul_of_nonneg_right hxx (mul_nonneg hC.le hP.le)
    apply (mul_le_mul_of_nonneg_left htri (by positivity : 0≤2*I)).trans
    nlinarith only [mul_le_mul_of_nonneg_right hIP (show 0≤C*u*L by positivity),hspace',hrest,
      mul_nonneg hC.le hP.le,div_nonneg (sq_nonneg H) hC.le]
  · have hx₁ : 1/4≤|x| := (lt_of_not_ge hn).le
    have hI₈ : I≤8 := hD.trans ((div_le_iff₀ hx₀).mpr (by linarith))
    have hI₂ : I^2≤68*P := by
      apply (pow_le_pow_left₀ hI hD 2).trans
      rw [hPr,div_pow,sq_abs,mul_one_div,div_le_div_iff₀ (by simpa only [sq_abs] using sq_pos_of_pos hx₀) (by positivity)]
      nlinarith only [sq_abs x,pow_le_pow_left₀ (by norm_num) hx₁ 2]
    have hY : 2*I*|H|≤C*I^2+H^2/C := by
      apply (le_of_mul_le_mul_right _ hC)
      rw [add_mul,div_mul_cancel₀ _ hC.ne']
      nlinarith only [sq_nonneg (C*I-|H|),sq_abs H]
    have htri := abs_sub H (star*P)
    rw [abs_mul,abs_of_pos hP] at htri
    have hstar' := mul_le_mul hI₈ hstar (abs_nonneg _) (by norm_num : (0:ℝ)≤8)
    apply (mul_le_mul_of_nonneg_left htri (by positivity : 0≤2*I)).trans
    nlinarith only [hY,mul_le_mul_of_nonneg_left hI₂ hC.le,mul_le_mul_of_nonneg_right hstar' hP.le,
      show 0≤C*u*L*(P*I) by positivity,mul_nonneg hC.le hW]

end Liu
