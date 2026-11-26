import Liu.LogTailEstimate
import Liu.TailPhysical

noncomputable section
open Set MeasureTheory Filter Real Complex
open scoped Topology ComplexConjugate
namespace Liu

/-- On the real observation line, the exact Green kernel supplies an L²
majorant for each field term with independent lower and upper parameters. -/
theorem rankField_trace_bound {p c : ℂ} (hp : p.im<0) (hc : c.im<0) (x : ℝ) :
    ‖rankField p c x‖ ≤ (2*(poleBound 1 p*poleBound 1 c))*isolatedTrace 0 1 x := by
  let K := poleBound 1 p*poleBound 1 c
  have M (q : ℂ) (hq : q.im<0) : 0≤poleBound 1 q := by unfold poleBound; have := neg_pos.mpr hq; positivity
  have hK : 0≤K := mul_nonneg (M _ hp) (M _ hc)
  obtain ⟨hi,he⟩ := isolatedDensity_integral zero_lt_one (by simp : (-I).im<0) x
  rw [rankField,norm_neg]
  apply (norm_integral_le_of_norm_le (hi.const_mul (2*K)) ?_).trans_eq
  · rw [integral_const_mul,he]; simp [K]
  · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
    have hy : 0≤w.im := le_of_lt hw
    have hZ : 0<‖w+I‖ := (show 0<(w+I).im by simp; linarith).trans_le (im_le_norm _)
    have hle : ‖w+I‖≤1+‖w‖ := (norm_add_le ..).trans_eq (by simp [add_comm])
    have hb := (rankSource_decay hp hc hy).trans (div_le_div_of_nonneg_left hK (sq_pos_of_pos hZ)
      (pow_le_pow_left₀ (norm_nonneg _) hle 2))
    have hcoef : 0≤2*w.im/‖w-(x:ℂ)‖^2 := by positivity
    rw [norm_mul,greenResolvent_boundary,norm_mul,norm_neg,norm_I,one_mul,Complex.norm_of_nonneg hcoef,
      isolatedDensity,sub_neg_eq_add]
    exact (mul_le_mul_of_nonneg_left hb hcoef).trans_eq (by ring)

theorem separated_term_bounds {p q : ℂ} (hp : p.im<0) (hq : 0<q.im) (x : ℝ) :
    ‖tailTerm true p q x‖ ≤ 2*(poleBound 1 p*poleBound 1 (conj q))*isolatedTrace 0 1 x ∧
    ‖tailTerm false q p x‖ ≤ 2*(poleBound 1 (conj q)*poleBound 1 p)*isolatedTrace 0 1 x := by
  have hc : (conj q).im<0 := by simpa using hq
  have h₁ := (tailTerm_real (p:=p) (c:=conj q) hp hc x).1
  have h₂ := (tailTerm_real (p:=conj q) (c:=p) hc hp x).2
  simp only [Complex.conj_conj] at h₁ h₂
  have h₃ := (tailTerm_real (p:=conj q) (c:=p) hc hp x).1
  have hb := rankField_trace_bound hp hc x
  have hb' := rankField_trace_bound hc hp x
  rw [rankField_log_formula hp hc (z:=(x:ℂ)) (by simp),Complex.conj_conj] at hb
  rw [rankField_log_formula hc hp (z:=(x:ℂ)) (by simp)] at hb'
  rw [h₁,h₂,Complex.norm_conj,h₃]
  exact ⟨hb,hb'⟩

end Liu
