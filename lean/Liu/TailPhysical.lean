import Liu.LogTailKernel

noncomputable section
open Set Real Polynomial
open scoped ComplexConjugate
namespace Liu

theorem tailTerm_real {p c : ℂ} (hp : p.im<0) (hc : c.im<0) (x : ℝ) :
    tailTerm true p (conj c) x = rationalLogTerm p (conj c) x ∧
    tailTerm false (conj p) c x = conj (tailTerm true p (conj c) x) := by
  have l₁ : 0<((x:ℂ)-p).im := by simp [hp]
  have l₂ : 0<(conj c-p).im := by simp; linarith
  have u₁ : ((x:ℂ)-conj c).im<0 := by simp [hc]
  have u₂ : (p-conj c).im<0 := by simp; linarith
  have hl₁ : 0<((x:ℂ)-c).im := by simp [hc]
  have hl₂ : 0<(conj p-c).im := by simp; linarith
  have hu₁ : ((x:ℂ)-conj p).im<0 := by simp [hp]
  have hu₂ : (c-conj p).im<0 := by simp; linarith
  have neq : (x:ℂ)≠conj c := by intro e; have h := congrArg Complex.im e; simp at h; linarith
  have L (z : ℂ) (hz : z.im ≠ 0) : conj (Complex.log z)=Complex.log (conj z) := by
    apply (Complex.log_conj _ _).symm
    intro he
    have h := Complex.arg_eq_pi_iff.mp he; exact hz h.2
  constructor
  · rw [rationalLogTerm,logChord_eq hp (by simpa using hc) (by simp),dslope_of_ne _ neq,slope_def_field]
    simp [tailTerm,sideLog,upperNodeLog_principal u₁,upperNodeLog_principal u₂,
      lowerNodeLog_principal l₁,lowerNodeLog_principal l₂]
  · simp only [tailTerm,sideLog,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true,
      lowerNodeLog_principal hl₁,lowerNodeLog_principal hl₂,upperNodeLog_principal hu₁,upperNodeLog_principal hu₂,
      lowerNodeLog_principal l₁,lowerNodeLog_principal l₂,upperNodeLog_principal u₁,upperNodeLog_principal u₂,
      map_sub,map_div₀,L _ l₁.ne',L _ l₂.ne',L _ u₁.ne,L _ u₂.ne,Complex.conj_conj,Complex.conj_ofReal]

def Pair.weightedZero (P : Pair) : ℂ := (P.a₁:ℂ)*P.w₂+(P.a₂:ℂ)*P.w₁
def Pair.tailNodes (P : Pair) : Fin 3 → ℂ := ![P.w₁,P.w₂,P.weightedZero]

theorem Pair.tailNodes_below (P : Pair) (i : Fin 3) : (P.tailNodes i).im<0 := by
  fin_cases i
  · exact P.hw₁
  · exact P.hw₂
  · change (P.weightedZero).im<0
    simp only [Pair.weightedZero,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    exact add_neg (mul_neg_of_pos_of_neg P.ha₁ P.hw₂) (mul_neg_of_pos_of_neg P.ha₂ P.hw₁)

theorem Pair.unit_numerator_roots (P : Pair) (hm : P.a₁+P.a₂=1) :
    P.toPick.numeratorPoly.roots={P.weightedZero} := by
  have h₁ : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h₂ : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  have hsum : (P.a₁:ℂ)+(P.a₂:ℂ)=1 := by exact_mod_cast hm
  have he : P.toPick.numeratorPoly = -(X-C P.weightedZero) := by
    simp only [PickSum.numeratorPoly,Fin.sum_univ_two,PickSum.erasedFactor,h₁,h₂,Finset.prod_singleton,
      Pair.weightedZero,map_add,map_mul,map_neg]
    change -(C (P.a₁:ℂ))*(X-C P.w₂) + -(C (P.a₂:ℂ))*(X-C P.w₁) =
      -(X-(C (P.a₁:ℂ)*C P.w₂+C (P.a₂:ℂ)*C P.w₁))
    have hab := congrArg (C : ℂ → ℂ[X]) hsum
    rw [map_add,map_one] at hab
    linear_combination -X*hab
  rw [he,roots_neg,roots_X_sub_C]

theorem Pair.tail_field (P : Pair) (hm : P.a₁+P.a₂=1) (x : ℝ) :
    let A := P.tailNodes
    let B := fun i => conj (A i)
    tailSide true A B P.a₁ P.a₂ x=field P.toPick.value x ∧
      tailSide false B A P.a₁ P.a₂ x=conj (field P.toPick.value x) := by
  let A := P.tailNodes
  let B := fun i => conj (A i)
  have T (i j : Fin 3) := tailTerm_real (P.tailNodes_below i) (P.tailNodes_below j) x
  have e := P.toPick.rational_log_field (z:=(x:ℂ)) (by simp)
  simp only [PickSum.signedNodes,P.unit_numerator_roots hm,Multiset.map_singleton,Multiset.sum_singleton,Fin.sum_univ_two] at e
  change field P.toPick.value x = _ at e
  have e' : field P.toPick.value x = (Complex.I/2)*
      (-(P.a₁:ℂ)*(rationalLogTerm (A 0) (B 2) x-(rationalLogTerm (A 0) (B 0) x+rationalLogTerm (A 0) (B 1) x))+
      -(P.a₂:ℂ)*(rationalLogTerm (A 1) (B 2) x-(rationalLogTerm (A 1) (B 0) x+rationalLogTerm (A 1) (B 1) x))) := e
  have H (i j : Fin 3) : tailTerm true (A i) (B j) x=rationalLogTerm (A i) (B j) x := (T i j).1
  have H' (i j : Fin 3) : tailTerm false (B i) (A j) x=conj (tailTerm true (A i) (B j) x) := (T i j).2
  change tailSide true A B _ _ x=_ ∧ tailSide false B A _ _ x=_
  have first : tailSide true A B P.a₁ P.a₂ x=field P.toPick.value x := by
    rw [e']; simp only [tailSide,tailSingle,tailCross,fieldCoefficient,if_true,Fin.castSucc_zero,show (1:Fin 2).castSucc=(1:Fin 3) by decide]
    change _=_
    simp_rw [H]; ring
  refine ⟨first,?_⟩
  rw [←first]
  simp only [tailSide,tailSingle,tailCross,fieldCoefficient,if_true,Bool.false_eq_true,if_false,
    map_add,map_sub,map_mul,map_div₀,Complex.conj_I,Complex.conj_ofReal,map_ofNat]
  simp_rw [H']

/-- On real configurations the continued product is exactly the physical
flux density with both squared-mass single-pole densities removed. -/
theorem Pair.tail_subtraction_agrees (P : Pair) (hm : P.a₁+P.a₂=1) (x : ℝ) :
    let h := fun S : ℂ → ℂ => ‖field S x‖^2-k₀*‖S x‖^2
    subtractedTail P.tailNodes (fun i => conj (P.tailNodes i)) P.a₁ P.a₂ x =
      ((h P.toPick.value-P.a₁^2*h (pole 1 P.w₁)-P.a₂^2*h (pole 1 P.w₂):ℝ):ℂ) := by
  let A := P.tailNodes
  let B := fun i => conj (A i)
  have single (i : Fin 2) :
      tailSingle true A B i x = field (pole 1 (A i.castSucc)) x ∧
      tailSingle false B A i x = conj (field (pole 1 (A i.castSucc)) x) := by
    have ht := tailTerm_real (P.tailNodes_below i.castSucc) (P.tailNodes_below i.castSucc) x
    have he := diagonal_log_field (P.tailNodes_below i.castSucc) (z:=(x:ℂ)) (by simp)
    change field (pole 1 (A i.castSucc)) x = _ at he
    constructor
    · exact (congrArg (fun t => (Complex.I/2)*t) ht.1).trans he.symm
    · change -Complex.I/2*tailTerm false (B i.castSucc) (A i.castSucc) x=_
      rw [he,map_mul,map_div₀,Complex.conj_I,map_ofNat,←ht.1]
      exact congrArg (fun t => -Complex.I/2*t) ht.2
  have hS (p : ℂ) : tailPole p x = pole 1 p x := by simp [tailPole,pole,div_eq_mul_inv]
  have hSb (p : ℂ) : tailPole (conj p) x = conj (tailPole p x) := by simp [tailPole]
  have hP : (P.a₁:ℂ)*tailPole (A 0) x+(P.a₂:ℂ)*tailPole (A 1) x=P.toPick.value x := by
    simp [PickSum.value,Fin.sum_univ_two,Pair.toPick,A,Pair.tailNodes,pole,tailPole,div_eq_mul_inv,add_comm]
  have hQ : (P.a₁:ℂ)*tailPole (B 0) x+(P.a₂:ℂ)*tailPole (B 1) x=conj (P.toPick.value x) := by
    rw [←hP]; simp [B,hSb]
  have H : tailSide true A B P.a₁ P.a₂ x=field P.toPick.value x ∧
      tailSide false B A P.a₁ P.a₂ x=conj (field P.toPick.value x) := P.tail_field hm x
  change subtractedTail A B P.a₁ P.a₂ x = _
  unfold subtractedTail
  simp only [H.1,H.2,hP,hQ,(single 0).1,(single 0).2,(single 1).1,(single 1).2,
    show (0:Fin 2).castSucc=(0:Fin 3) by decide,show (1:Fin 2).castSucc=(1:Fin 3) by decide]
  dsimp only [B]
  simp only [hSb,hS,mul_assoc (k₀:ℂ),Complex.mul_conj',Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow]
  rfl

end Liu
