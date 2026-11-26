import Liu.MovingLogTerms

noncomputable section
open Set MeasureTheory Filter Real Complex
open scoped Topology ComplexConjugate
namespace Liu

theorem moving_pole_dominated {U : Set ℂ} (hU : IsOpen U) (s : Bool) {p : ℂ → ℂ}
    (dp : DifferentiableOn ℂ p U) (hp : ∀ t∈U, orientedBelow s (p t)) :
    DominatedFamily 2 U (fun t x => tailPole (p t) (x:ℂ)) := by
  have hn (t : ℂ) (ht : t∈U) : (p t).im≠0 := by
    have h := hp t ht; cases s
    · exact (show 0<(p t).im from h).ne'
    · exact (show (p t).im<0 from h).ne
  refine ⟨fun _ => by unfold tailPole; fun_prop,fun x => ?_,?_⟩
  · refine ((dp.const_sub (x:ℂ)).inv (fun t ht => ?_)).neg
    intro h; apply hn t ht; simpa using (congrArg Complex.im (sub_eq_zero.mp h)).symm
  · intro c hc
    have hpc := (dp.differentiableAt (hU.mem_nhds hc)).continuousAt
    have nz := abs_ne_zero.mpr (hn c hc)
    have hcont : ContinuousAt (fun t => poleWeight (p t)) c := by unfold poleWeight; fun_prop (disch := assumption)
    have hnear := hcont.eventually_lt continuousAt_const (show poleWeight (p c)<poleWeight (p c)+1 by linarith)
    have hL := linePole_sq_integrable 0 zero_lt_one
    have hm : MemLp (fun x => ‖linePole 0 1 x‖) 2 volume := by
      exact (memLp_two_iff_integrable_sq (by unfold linePole; fun_prop)).mpr hL
    refine ⟨fun x => (poleWeight (p c)+1)*‖linePole 0 1 x‖,hm.const_smul (poleWeight (p c)+1),?_⟩
    filter_upwards [hnear,hU.mem_nhds hc] with t hK ht x
    have hb (q : ℂ) (hq : q.im<0) : ‖tailPole q (x:ℂ)‖≤poleWeight q*‖linePole 0 1 x‖ := by
      have h := pole_global_decay (a:=1) (w:=q) (z:=(x:ℂ)) zero_lt_one hq (by simp)
      have hJ : 0<‖(x:ℂ)+I‖ := (show 0<((x:ℂ)+I).im by simp).trans_le (im_le_norm _)
      have hX : ‖(x:ℂ)+I‖≤1+‖(x:ℂ)‖ := (norm_add_le ..).trans_eq (by simp [add_comm])
      have hb : poleBound 1 q=poleWeight q := by simp [poleBound,poleWeight,abs_of_neg hq]
      have h₀ : 0≤poleWeight q := by unfold poleWeight; positivity
      apply (le_trans _ (show poleWeight q/‖(x:ℂ)+I‖=poleWeight q*‖linePole 0 1 x‖ by simp [linePole,div_eq_mul_inv]).le)
      apply (le_trans _ (div_le_div_of_nonneg_left h₀ hJ hX))
      simpa [tailPole,pole,hb,one_div] using h
    apply (le_trans _ (mul_le_mul_of_nonneg_right hK.le (norm_nonneg _)))
    cases s
    · have ht' : 0<(p t).im := hp t ht
      have H := hb (conj (p t)) (by simpa using ht')
      have e : tailPole (conj (p t)) x=conj (tailPole (p t) x) := by simp [tailPole]
      simpa [e,poleWeight] using H
    · exact hb _ (hp t ht)

def singleDensity (p q z : ℂ) : ℂ :=
  (fieldCoefficient true*tailTerm true p q z)*(fieldCoefficient false*tailTerm false q p z) -
    (k₀:ℂ)*tailPole p z*tailPole q z

def totalDensity (P Q : Fin 3 → ℂ) (a b z : ℂ) : ℂ :=
  tailSide true P Q a b z * tailSide false Q P a b z -
    (k₀:ℂ)*(a*tailPole (P 0) z+b*tailPole (P 1) z)*(a*tailPole (Q 0) z+b*tailPole (Q 1) z)

theorem density_subtraction (P Q : Fin 3 → ℂ) (a b z : ℂ) :
    subtractedTail P Q a b z=totalDensity P Q a b z-a^2*singleDensity (P 0) (Q 0) z-b^2*singleDensity (P 1) (Q 1) z := rfl

theorem singleDensity_dominated {U : Set ℂ} (ho : IsOpen U) {p q : ℂ → ℂ}
    (dp : DifferentiableOn ℂ p U) (dq : DifferentiableOn ℂ q U)
    (hp : ∀ t∈U, (p t).im<0) (hq : ∀ t∈U, 0<(q t).im) :
    DominatedFamily 1 U (fun t x => singleDensity (p t) (q t) x) :=
  (((moving_term_dominated ho true dp dq hp hq).const_mul (fieldCoefficient true)).mul_two
    ((moving_term_dominated ho false dq dp hq hp).const_mul (fieldCoefficient false))).sub
      (((moving_pole_dominated ho true dp hp).const_mul (k₀:ℂ)).mul_two (moving_pole_dominated ho false dq hq))

theorem totalDensity_dominated {U : Set ℂ} (ho : IsOpen U) (P Q : Fin 3 → ℂ → ℂ) (a b : ℂ)
    (dp : ∀ j, DifferentiableOn ℂ (P j) U) (dq : ∀ j, DifferentiableOn ℂ (Q j) U)
    (hp : ∀ j t, t∈U → (P j t).im<0) (hq : ∀ j t, t∈U → 0<(Q j t).im) :
    DominatedFamily 1 U (fun t x => totalDensity (fun j => P j t) (fun j => Q j t) a b x) := by
  have side (s : Bool) (A B : Fin 3 → ℂ → ℂ) (da : ∀ j, DifferentiableOn ℂ (A j) U)
      (db : ∀ j, DifferentiableOn ℂ (B j) U) (ha : ∀ j t, t∈U → orientedBelow s (A j t))
      (hb : ∀ j t, t∈U → orientedBelow (!s) (B j t)) :
      DominatedFamily 2 U (fun t x => tailSide s (fun j => A j t) (fun j => B j t) a b x) := by
    have H (i j : Fin 3) := moving_term_dominated ho s (da i) (db j) (ha i) (hb j)
    let e := fieldCoefficient s
    simpa only [tailSide,tailSingle,tailCross,Fin.castSucc_zero,show (1:Fin 2).castSucc=(1:Fin 3) by decide,e] using ((((H 0 0).const_mul e).const_mul a).add (((H 1 1).const_mul e).const_mul b)).add
      (((((H 0 1).sub (H 0 2)).const_mul a).add (((H 1 0).sub (H 1 2)).const_mul b)).const_mul e)
  have S := ((moving_pole_dominated ho true (dp 0) (hp 0)).const_mul a).add
    ((moving_pole_dominated ho true (dp 1) (hp 1)).const_mul b)
  have T := ((moving_pole_dominated ho false (dq 0) (hq 0)).const_mul a).add
    ((moving_pole_dominated ho false (dq 1) (hq 1)).const_mul b)
  exact ((side true P Q dp dq hp hq).mul_two (side false Q P dq dp hq hp)).sub ((S.const_mul (k₀:ℂ)).mul_two T)

end Liu
