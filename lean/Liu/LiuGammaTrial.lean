module

public import Liu.CapExpansion
public import Liu.GaussDerivatives

@[expose] public section

noncomputable section
open Set Filter Real
open scoped Topology
namespace Liu

def symmetricGammaLog (t : ℝ) := Real.log (Real.Gamma (1+t))+Real.log (Real.Gamma (1-t))

private theorem logGamma_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => Real.log (Real.Gamma y)) (psi x) x := by
  have h := (gamma_psi_derivative hx).log (Real.Gamma_pos_of_pos hx).ne'
  simpa [mul_div_cancel_left₀ _ (Real.Gamma_pos_of_pos hx).ne'] using h

theorem symmetricGammaLog_limit :
    Tendsto (fun t : ℝ => symmetricGammaLog t/t^2) (𝓝[≠] 0) (𝓝 (π^2/6)) := by
  let D := fun t : ℝ => psi (1+t)-psi (1-t)
  have hd (t : ℝ) (ht : |t|<1) : HasDerivAt symmetricGammaLog (D t) t := by
    change HasDerivAt (fun x => Real.log (Real.Gamma (1+x))+Real.log (Real.Gamma (1-x))) _ t
    have h₁ := logGamma_deriv (show 0<1+t by linarith [(abs_lt.mp ht).1])
    have h₂ := logGamma_deriv (show 0<1-t by linarith [(abs_lt.mp ht).2])
    simpa [symmetricGammaLog,D,Function.comp_def,sub_eq_add_neg] using
      (h₁.comp t ((hasDerivAt_id t).const_add 1)).fun_add (h₂.comp t ((hasDerivAt_id t).const_sub 1))
  have hψ : HasDerivAt psi (π^2/6) 1 := by
    have g := hasDerivAt_psi_series (x:=1) zero_lt_one
    have eq : trigamma 1=π^2/6 := by
      obtain ⟨C,hC,h⟩ := trigamma_one_expansion
      have he := h 0 (by simp); apply sub_eq_zero.mp; simpa using he
    rwa [←trigamma_eq_series zero_lt_one,eq] at g
  have dD : HasDerivAt D (2*(π^2/6)) 0 := by
    have h₁ : HasDerivAt psi (π^2/6) (1+(0:ℝ)) := by simpa using hψ
    have h₂ : HasDerivAt psi (π^2/6) (1-(0:ℝ)) := by simpa using hψ
    convert (h₁.comp 0 ((hasDerivAt_id (0:ℝ)).const_add 1)).sub (h₂.comp 0 ((hasDerivAt_id (0:ℝ)).const_sub 1)) using 1
    · rfl
    · ring
  have H : Tendsto (fun t : ℝ => D t/t) (𝓝[≠] 0) (𝓝 (2*(π^2/6))) := by
    have H : Tendsto (fun t => slope D 0 t) (𝓝[≠] 0) (𝓝 (2*(π^2/6))) := hasDerivAt_iff_tendsto_slope.mp dD
    simpa [slope_def_field,D] using H
  apply HasDerivAt.lhopital_zero_nhdsNE (f':=D) (g':=fun x : ℝ => 2*x)
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℝ) zero_lt_one)] with t ht
    exact hd t (by simpa [Real.dist_eq] using ht)
  · exact .of_forall fun t => by simpa using (hasDerivAt_pow 2 t)
  · filter_upwards [self_mem_nhdsWithin] with t (ht : t≠0) using mul_ne_zero (by norm_num) ht
  · simpa [symmetricGammaLog] using (hd 0 (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · simpa using (continuousAt_id (x:=(0:ℝ))).tendsto.pow 2 |>.mono_left nhdsWithin_le_nhds
  · convert H.div_const 2 using 1
    · funext t; ring
    · congr 1; ring

end Liu
