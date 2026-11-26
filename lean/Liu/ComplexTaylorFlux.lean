import Liu.CentredDensity

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology ComplexConjugate
namespace Liu

/-- The boundary flux extended by the two independent partner factors. -/
def pairedBoundaryFlux (P Q : Fin 3 → ℂ) (a b : ℂ) : ℂ :=
  (∫ x : ℝ, totalDensity P Q a b x)/(Real.pi:ℂ)

theorem Pair.pairedBoundaryFlux_actual (P : Pair) (hm : P.a₁+P.a₂=1) :
    pairedBoundaryFlux P.tailNodes (fun i => conj (P.tailNodes i)) P.a₁ P.a₂ = (boundaryFlux P.toPick.value:ℂ) := by
  let A := P.tailNodes
  let B := fun i => conj (A i)
  have he (x : ℝ) : totalDensity A B P.a₁ P.a₂ x =
      ((‖field P.toPick.value x‖^2-k₀*‖P.toPick.value x‖^2:ℝ):ℂ) := by
    have hS : (P.a₁:ℂ)*tailPole (A 0) x+(P.a₂:ℂ)*tailPole (A 1) x=P.toPick.value x := by
      simp [PickSum.value,Fin.sum_univ_two,Pair.toPick,A,Pair.tailNodes,pole,tailPole,div_eq_mul_inv,add_comm]
    have hQ : (P.a₁:ℂ)*tailPole (B 0) x+(P.a₂:ℂ)*tailPole (B 1) x=conj (P.toPick.value x) := by
      rw [←hS]; simp [B,tailPole]
    have H : tailSide true A B P.a₁ P.a₂ x=field P.toPick.value x ∧
        tailSide false B A P.a₁ P.a₂ x=conj (field P.toPick.value x) := P.tail_field hm x
    rw [totalDensity,H.1,H.2,hS,hQ,mul_assoc (k₀:ℂ),Complex.mul_conj',Complex.mul_conj']
    push_cast; rfl
  change (∫ x : ℝ, totalDensity A B P.a₁ P.a₂ x)/(Real.pi:ℂ)=_
  simp_rw [he,integral_complex_ofReal,boundaryFlux,Complex.ofReal_div]

/-- Lemma 6.8. The path runs from the mass centres to the actual lower nodes
and upper partners. The Taylor coefficients are the true analytic value
and derivative at zero, including at complex masses and positions. -/
theorem centred_taylor_flux (a b : ℂ) (hab : a+b=1) (P Q : Fin 3 → ℂ)
    (hP : P 2=a*P 1+b*P 0) (hQ : Q 2=a*Q 1+b*Q 0)
    (hsep : ∀ r ∈ Icc (0:ℝ) 1, ∀ j, (movingNode a b P j r).im<0 ∧ 0<(movingNode a b Q j r).im) :
    let H := movedSubtraction a b P Q
    let D := fun x => deriv (fun t => H t x) 0
    (∃ U : Set ℂ, IsOpen U ∧ (∀ r∈Icc (0:ℝ) 1, (r:ℂ)∈U) ∧
      ∀ x, AnalyticOnNhd ℂ (fun t => H t x) U) ∧
    (∀ x, H 0 x=2*a*b*singleDensity (massCentre a b P) (massCentre a b Q) x) ∧
    Integrable (H 0) ∧ Integrable D ∧ (∫ x, H 0 x)=0 ∧ (∫ x, D x)=0 ∧
    (Real.pi:ℂ)*pairedBoundaryFlux P Q a b = ∫ x, H 1 x-H 0 x-D x := by
  let H := movedSubtraction a b P Q
  let F := movedFullDensity a b P Q
  let U := movementDomain a b P Q
  have hopen := movement_open a b P Q
  have h₀ : (0:ℂ)∈U := by simpa only [U,movementDomain,mem_setOf_eq,ofReal_zero] using hsep 0 (by simp)
  have h₁ : (1:ℂ)∈U := by simpa only [U,movementDomain,mem_setOf_eq,ofReal_one] using hsep 1 (by simp)
  obtain ⟨hF,hH⟩ := movement_dominated a b P Q
  have e : (fun t => ∫ x, H t x) =ᶠ[𝓝 0] (fun t => ∫ x, F t x) :=
    by filter_upwards [hopen.mem_nhds h₀] with t ht using moved_integrals_agree a b P Q ht
  have df := hF.integral_hasDeriv hopen h₀
  have dz (x : ℝ) : deriv (fun t => F t x) 0=0 := (movedFull_deriv_zero a b hab P Q hP hQ h₀ x).deriv
  change HasDerivAt (fun t => ∫ x, F t x) (∫ x, deriv (fun t => F t x) 0) 0 at df
  simp only [dz,integral_zero] at df
  have hd := hH.integral_hasDeriv hopen h₀
  have E : (∫ x, deriv (fun t => H t x) 0)=0 := hd.unique (df.congr_of_eventuallyEq e)
  have hp : (massCentre a b P).im<0 := by simpa [movingNode_zero] using (h₀ 0).1
  have hq : 0<(massCentre a b Q).im := by simpa [movingNode_zero] using (h₀ 0).2
  have c₀ : (∫ x, H 0 x)=0 := by
    simp_rw [H,movedSubtraction_at_zero a b hab,integral_const_mul,single_partner_integral_zero hp hq,mul_zero]
  have I₀ : Integrable (H 0) :=  hH.integrable h₀
  have I₁ : Integrable (H 1) :=  hH.integrable h₁
  have ID : Integrable (fun x => deriv (fun t => H t x) 0) :=  hH.deriv_integrable hopen h₀
  refine ⟨⟨U,hopen,hsep,fun x => (hH.differentiable x).analyticOnNhd hopen⟩,
    movedSubtraction_at_zero a b hab P Q,I₀,ID,c₀,E,?_⟩
  change _ = ∫ x, H 1 x-H 0 x-deriv (fun t => H t x) 0
  have Isub : Integrable (fun x => H 1 x-H 0 x) := I₁.sub I₀
  rw [integral_sub Isub ID,integral_sub I₁ I₀,c₀,E,sub_zero,sub_zero]
  have hLast : (∫ x, H 1 x)=∫ x : ℝ, totalDensity P Q a b (x:ℂ) := by
    rw [show (∫ x,H 1 x)=∫ x,F 1 x from moved_integrals_agree a b P Q h₁]
    simp [F,movedFullDensity,movingNode_one]
  rw [hLast,pairedBoundaryFlux]; field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

end Liu
