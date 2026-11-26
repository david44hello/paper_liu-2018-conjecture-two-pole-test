import Liu.RationalLogTerm
import Liu.PolarResolvent
import Liu.DiagonalLogField

noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu

theorem rationalLogTerm_polar_analytic (p c : ℂ) {z : ℂ} (hz : 0≤z.im) :
    AnalyticOnNhd ℂ (fun t => rationalLogTerm (polarPole p c t) (conj (polarPole p c (conj t))) z)
      (polarWindow p c) := by
  let P := polarPole p c
  let Q := fun t => conj (P (conj t))
  let U := polarWindow p c
  have hU : IsOpen U := polar_window_open p c
  have hp : Differentiable ℂ P := (differentiable_id.mul_const _).const_add _
  have hq : Differentiable ℂ Q := by
    intro t
    simpa only [Q,Function.comp_def,Complex.conj_conj] using (hp (conj t)).conj_conj
  have hQ {t : ℂ} (ht : t∈U) : 0<(Q t).im := by simpa [Q] using (show (P (conj t)).im<0 from ht.2)
  have hslit {a : ℂ} (h : a.im≠0) : a∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr h)
  have hF : DifferentiableOn ℂ (fun t => (Complex.log (conj z-Q t)-Complex.log (P t-Q t))/(z-P t)) U := by
    intro t ht
    have h₁ : (conj z - Q t) ∈ Complex.slitPlane := hslit (by simp; linarith [hQ ht])
    have h₂ : P t-Q t ∈ Complex.slitPlane := hslit (by simp; linarith [hQ ht,show (P t).im<0 from ht.1])
    have hn : z-P t ≠ 0 := by intro e; rw [sub_eq_zero.mp e] at hz; linarith [show (P t).im<0 from ht.1]
    exact (((((hq t).const_sub (conj z)).clog h₁).sub (((hp t).sub (hq t)).clog h₂)).div ((hp t).const_sub z) hn).differentiableWithinAt
  have hC : DifferentiableOn ℂ (fun t => logChord (P t) (Q t) z) U := by
    unfold logChord
    simp_rw [intervalIntegral.integral_of_le zero_le_one]
    apply differentiableOn_local_integral (volume.restrict (Ioc (0:ℝ) 1)) hU
    · intro t; fun_prop
    · filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (α:=ℝ) (a:=0) (b:=1))] with y hy
      intro t ht
      have hi := chord_im_bound (p:=P t) (hQ ht).le hz (Ioc_subset_Icc_self hy)
      have hp₀ : (P t).im<0 := ht.1
      have hn : Q t+(y:ℂ)*(z-Q t)-P t ≠ 0 := by intro e; rw [e] at hi; simp at hi; linarith
      exact ((((hq t).add (((hq t).const_sub z).const_mul (y:ℂ))).sub (hp t)).inv hn).differentiableWithinAt
    · intro t ht
      let δ := -(P t).im/2
      have ht₁ : (P t).im<0 := ht.1
      have hδ : 0<δ := by dsimp [δ]; linarith
      have hnear : ∀ᶠ w in 𝓝 t, (P w).im < -δ :=
        (Complex.continuous_im.continuousAt.comp (hp t).continuousAt).eventually_lt continuousAt_const (by dsimp [δ]; linarith)
      refine ⟨fun _ => δ⁻¹,integrable_const _,U∩{w | (P w).im < -δ},inter_mem (hU.mem_nhds ht) hnear,?_⟩
      filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioc (α:=ℝ) (a:=0) (b:=1))] with y hy
      intro w hw
      have hi := chord_im_bound (p:=P w) (hQ hw.1).le hz (Ioc_subset_Icc_self hy)
      rw [norm_inv]
      apply inv_anti₀ hδ
      apply le_trans _ (Complex.im_le_norm _)
      linarith [show (P w).im < -δ from hw.2]
  exact (hF.sub hC).analyticOnNhd hU

/-- Polarization of the actual Green transform identifies the rank-one
kernel with the rational-log term for all independent lower p and c. -/
theorem rankField_log_formula {p c z : ℂ} (hp : p.im<0) (hc : c.im<0) (hz : 0≤z.im) :
    rankField p c z = rationalLogTerm p (conj c) z := by
  have H := polar_identity hp hc (rankField_polar_analytic p c hz) (rationalLogTerm_polar_analytic p c hz)
    (fun t ht => by
      simp only [Complex.conj_ofReal]
      have hp' : (polarPole p c t).im<0 := ht.1
      have h₁ := rankField_diagonal hp' hz
      have h₂ := diagonal_log_field hp' hz
      exact mul_left_cancel₀ (div_ne_zero Complex.I_ne_zero (by norm_num : (2:ℂ)≠0)) (h₁.symm.trans h₂))
  obtain ⟨hi,hn,_,_⟩ := polar_points hp hc
  simpa only [hi,Complex.conj_I,hn] using H

end Liu
