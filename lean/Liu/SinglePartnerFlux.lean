module

public import Liu.PairedFlux

@[expose] public section

noncomputable section
open Set MeasureTheory Filter Real Complex
open scoped Topology ComplexConjugate
namespace Liu

theorem singleDensity_real {p : ℂ} (hp : p.im<0) (x : ℝ) :
    singleDensity p (conj p) (x:ℂ)=((‖field (pole 1 p) x‖^2-k₀*‖pole 1 p x‖^2:ℝ):ℂ) := by
  have hd := diagonal_log_field hp (z:=(x:ℂ)) (by simp)
  have ht := tailTerm_real hp hp x
  have e : fieldCoefficient true*tailTerm true p (conj p) x=field (pole 1 p) x :=
    (congrArg (fun t => (I/2)*t) ht.1).trans hd.symm
  have e' : fieldCoefficient false*tailTerm false (conj p) p x=conj (field (pole 1 p) x) := by
    rw [←e,map_mul,←ht.2]
    simp [fieldCoefficient,map_ofNat]
  have hv : tailPole p x=pole 1 p x := by simp [tailPole,pole,div_eq_mul_inv]
  have hv' : tailPole (conj p) x=conj (pole 1 p x) := by rw [←hv]; simp [tailPole]
  rw [singleDensity,e,e',hv,hv',mul_assoc (k₀:ℂ),Complex.mul_conj',Complex.mul_conj']
  push_cast; rfl

/-- The line integral of the isolated density vanishes even for an
independent upper partner. The real diagonal determines its continuation. -/
theorem single_partner_integral_zero {p q : ℂ} (hp : p.im<0) (hq : 0<q.im) :
    (∫ x : ℝ, singleDensity p q (x:ℂ))=0 := by
  let c := conj q
  have hc : c.im<0 := by simpa [c] using hq
  let P := polarPole p c
  let Q := fun t => conj (P (conj t))
  let U := polarWindow p c
  have hU := polar_window_open p c
  have dp : Differentiable ℂ P := (differentiable_id.mul_const _).const_add _
  have dq : Differentiable ℂ Q := fun t => by simpa only [Q,Function.comp_def,Complex.conj_conj] using (dp (conj t)).conj_conj
  have hf := singleDensity_dominated (U:=U) hU dp.differentiableOn dq.differentiableOn
    (fun t ht => ht.1) (fun t ht => by simpa [Q] using (show (P (conj t)).im<0 from ht.2))
  let F := fun t => ∫ x : ℝ, singleDensity (P t) (Q t) (x:ℂ)
  have hF : AnalyticOnNhd ℂ F U :=
    (show DifferentiableOn ℂ F U from fun _ ht => (hf.integral_hasDeriv hU ht).differentiableAt.differentiableWithinAt).analyticOnNhd hU
  have H := polar_identity hp hc hF (g:=fun _ => (0:ℂ)) analyticOnNhd_const (fun r hr => by
    have h : (P r).im<0 := hr.1
    have eq : Q r=conj (P r) := by simp [Q]
    have hb := single_pole_flux_zero (P r).re (m:=1) (b:= -(P r).im) zero_lt_one (neg_pos.mpr h)
    have ep : (((P r).re:ℝ):ℂ)-((-(P r).im:ℝ):ℂ)*I=P r := by apply Complex.ext <;> simp
    rw [ep,div_eq_zero_iff] at hb
    have h₀ := hb.resolve_right pi_ne_zero
    change (∫ x : ℝ, singleDensity (P r) (Q r) (x:ℂ))=0
    simp_rw [eq,singleDensity_real h,integral_complex_ofReal,h₀,Complex.ofReal_zero])
  obtain ⟨hi,hn,_,_⟩ := polar_points hp hc
  simpa only [F,P,Q,hi,Complex.conj_I,hn,c,Complex.conj_conj] using H

end Liu
