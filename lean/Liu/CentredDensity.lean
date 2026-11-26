import Liu.SinglePartnerFlux
import Liu.CentredMovement

noncomputable section
open Set MeasureTheory Filter Real Complex
open scoped Topology
namespace Liu

def movementDomain (a b : ℂ) (P Q : Fin 3 → ℂ) : Set ℂ :=
  {t | ∀ i, (movingNode a b P i t).im<0 ∧ 0<(movingNode a b Q i t).im}

theorem movement_open (a b : ℂ) (P Q : Fin 3 → ℂ) : IsOpen (movementDomain a b P Q) := by
  have cont (A : Fin 3 → ℂ) (i : Fin 3) : Continuous (movingNode a b A i) :=
    continuous_iff_continuousAt.mpr (fun t => (movingNode_deriv ..).continuousAt)
  have h (i : Fin 3) : IsOpen {t | (movingNode a b P i t).im<0 ∧ 0<(movingNode a b Q i t).im} :=
    (isOpen_lt ((continuous_im.comp (cont P i))) continuous_const).inter
      (isOpen_lt continuous_const (continuous_im.comp (cont Q i)))
  simpa only [movementDomain,setOf_forall] using isOpen_iInter_of_finite h

def movedSubtraction (a b : ℂ) (P Q : Fin 3 → ℂ) (t : ℂ) (x : ℝ) : ℂ :=
  subtractedTail (fun i => movingNode a b P i t) (fun i => movingNode a b Q i t) a b x

def movedFullDensity (a b : ℂ) (P Q : Fin 3 → ℂ) (t : ℂ) (x : ℝ) : ℂ :=
  totalDensity (fun i => movingNode a b P i t) (fun i => movingNode a b Q i t) a b x

theorem movement_dominated (a b : ℂ) (P Q : Fin 3 → ℂ) :
    let U := movementDomain a b P Q
    DominatedFamily 1 U (movedFullDensity a b P Q) ∧ DominatedFamily 1 U (movedSubtraction a b P Q) := by
  let U := movementDomain a b P Q
  have ho := movement_open a b P Q
  have d (A : Fin 3 → ℂ) (j : Fin 3) : DifferentiableOn ℂ (movingNode a b A j) U :=
    fun t _ => (movingNode_deriv ..).differentiableAt.differentiableWithinAt
  have h := totalDensity_dominated ho (movingNode a b P) (movingNode a b Q) a b (d P) (d Q)
    (fun j t ht => (ht j).1) (fun j t ht => (ht j).2)
  have hs (j : Fin 3) := singleDensity_dominated ho (d P j) (d Q j) (fun t ht => (ht j).1) (fun t ht => (ht j).2)
  exact ⟨h,(h.sub ((hs 0).const_mul (a^2))).sub ((hs 1).const_mul (b^2))⟩

theorem movedSubtraction_at_zero (a b : ℂ) (hab : a+b=1) (P Q : Fin 3 → ℂ) (x : ℝ) :
    movedSubtraction a b P Q 0 x=2*a*b*singleDensity (massCentre a b P) (massCentre a b Q) x := by
  simp only [movedSubtraction,subtractedTail,tailSide,tailCross,tailSingle,movingNode_zero,singleDensity,
    sub_self,mul_zero,add_zero]
  have hb : b=1-a := by linear_combination hab
  rw [hb]; ring

theorem movedFull_deriv_zero (a b : ℂ) (hab : a+b=1) (P Q : Fin 3 → ℂ)
    (hP : P 2=a*P 1+b*P 0) (hQ : Q 2=a*Q 1+b*Q 0) (h₀ : (0:ℂ)∈movementDomain a b P Q) (x : ℝ) :
    HasDerivAt (fun t => movedFullDensity a b P Q t x) 0 0 := by
  have hp : (massCentre a b P).im<0 := by simpa only [movingNode_zero] using (h₀ 0).1
  have hq : 0<(massCentre a b Q).im := by simpa only [movingNode_zero] using (h₀ 0).2
  have A := centred_field_deriv true a b hab P Q hQ hp hq x
  have B := centred_field_deriv false a b hab Q P hP hq hp x
  have C := centred_pick_deriv true a b hab P hp x
  have D := centred_pick_deriv false a b hab Q hq x
  simpa only [movedFullDensity,totalDensity,zero_mul,mul_zero,zero_add,sub_zero] using (A.fun_mul B).fun_sub ((C.const_mul (k₀:ℂ)).fun_mul D)

theorem moved_integrals_agree (a b : ℂ) (P Q : Fin 3 → ℂ) {t : ℂ} (ht : t∈movementDomain a b P Q) :
    (∫ x, movedSubtraction a b P Q t x)=∫ x, movedFullDensity a b P Q t x := by
  have hf := (movement_dominated a b P Q).1.integrable ht
  have ho := movement_open a b P Q
  have d (A : Fin 3 → ℂ) (j : Fin 3) : DifferentiableOn ℂ (movingNode a b A j) (movementDomain a b P Q) :=
    fun u _ => (movingNode_deriv ..).differentiableAt.differentiableWithinAt
  have hs (j : Fin 3) := (singleDensity_dominated ho (d P j) (d Q j) (fun u hu => (hu j).1)
    (fun u hu => (hu j).2)).integrable ht
  have hz (j : Fin 3) := single_partner_integral_zero (ht j).1 (ht j).2
  let S := fun (j : Fin 3) (x : ℝ) => singleDensity (movingNode a b P j t) (movingNode a b Q j t) (x:ℂ)
  change (∫ x, movedFullDensity a b P Q t x-a^2*S 0 x-b^2*S 1 x)=_
  have iA : Integrable (fun x => a^2*S 0 x) := (hs 0).const_mul _
  have iB : Integrable (fun x => b^2*S 1 x) := (hs 1).const_mul _
  have iF : Integrable (fun x => movedFullDensity a b P Q t x-a^2*S 0 x) := hf.sub iA
  rw [integral_sub iF iB,integral_sub hf iA,integral_const_mul,integral_const_mul]
  simp [S,hz]

end Liu
