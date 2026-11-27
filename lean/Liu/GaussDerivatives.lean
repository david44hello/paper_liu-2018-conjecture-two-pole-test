module

public import Liu.CapExpansion

@[expose] public section

noncomputable section
open Real Set Filter
open scoped Topology
namespace Liu

def discGamma (a b : ℝ) := Gamma (2-a-b)/(Gamma (2-a)*Gamma (2-b))

theorem gamma_psi_derivative {x : ℝ} (hx : 0<x) : HasDerivAt Gamma (Gamma x*psi x) x := by
  have hn := (Gamma_pos_of_pos hx).ne'
  rw [psi_eq_gamma_ratio hx,show Gamma x*(deriv Gamma x/Gamma x)=deriv Gamma x by field_simp]
  exact (differentiableAt_Gamma (fun n => by have := Nat.cast_nonneg (α:=ℝ) n; linarith)).hasDerivAt

theorem discGamma_left {a b : ℝ} (h₁ : 0<2-a-b) (h₂ : 0<2-a) (h₃ : 0<2-b) :
    HasDerivAt (fun x => discGamma x b) (discGamma a b*(psi (2-a)-psi (2-a-b))) a := by
  have da := (hasDerivAt_id a).const_sub 2
  have hn := (gamma_psi_derivative h₁).comp a (da.sub_const b)
  have hd := ((gamma_psi_derivative h₂).comp a da).mul_const (Gamma (2-b))
  have H := hn.div hd (mul_ne_zero (Gamma_pos_of_pos h₂).ne' (Gamma_pos_of_pos h₃).ne')
  convert H using 1
  · rfl
  · dsimp only [discGamma,id_eq,Function.comp_apply]
    field_simp [(Gamma_pos_of_pos h₂).ne',(Gamma_pos_of_pos h₃).ne']; ring

theorem discGamma_right {a b : ℝ} (h₁ : 0<2-a-b) (h₂ : 0<2-a) (h₃ : 0<2-b) :
    HasDerivAt (discGamma a) (discGamma a b*(psi (2-b)-psi (2-a-b))) b := by
  have hsym (x y : ℝ) : discGamma x y=discGamma y x := by unfold discGamma; rw [show 2-x-y=2-y-x by ring,mul_comm]
  have hh := discGamma_left (a:=b) (b:=a) (by linarith) h₃ h₂
  rw [hsym b a,show 2-b-a=2-a-b by ring] at hh
  exact hh.congr_of_eventuallyEq (Eventually.of_forall fun x => hsym a x)

theorem discGamma_mixed {a b : ℝ} (h₁ : 0<2-a-b) (h₂ : 0<2-a) (h₃ : 0<2-b) :
    HasDerivAt (fun y => discGamma a y*(psi (2-a)-psi (2-a-y)))
      (discGamma a b*((psi (2-a)-psi (2-a-b))*(psi (2-b)-psi (2-a-b))+trigamma (2-a-b))) b := by
  have hp : HasDerivAt psi (trigamma (2-a-b)) (2-a-b) := (hasDerivAt_psi_series h₁).differentiableAt.hasDerivAt
  have dv := (hp.comp b ((hasDerivAt_id b).const_sub (2-a))).const_sub (psi (2-a))
  convert (discGamma_right h₁ h₂ h₃).mul dv using 1
  · rfl
  · simp only [id_eq,Function.comp_apply]; ring

end Liu
