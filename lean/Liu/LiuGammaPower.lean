module

public import Liu.LiuGammaTrial
public import Liu.SlopeFormula

@[expose] public section

noncomputable section
open Set Filter Real
open scoped Topology
namespace Liu

/-- Liu's proposed norm for the unweighted half-plane Bergman projection.
The second argument is 2/p' for the conjugate exponent p'. -/
def liuNorm (p : ℝ) := Real.Gamma (2/p)*Real.Gamma (2-2/p)

theorem liuNorm_pos {p : ℝ} (hp : 1<p) : 0<liuNorm p := by
  have h : 0<p := by linarith
  apply mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos _)
  rw [sub_pos,div_lt_iff₀ h]; linarith

/-- The actual gamma product raised to p has quadratic coefficient π²/12. -/
theorem liuNorm_power_limit :
    Tendsto (fun d : ℝ => ((liuNorm (2+d))^(2+d)-1)/d^2) (𝓝[≠] 0) (𝓝 k₀) := by
  let T := fun d : ℝ => -d/(2+d)
  let P := fun d : ℝ => (2+d)*symmetricGammaLog (T d)
  let L := 𝓝[≠] (0:ℝ)
  have hd : Tendsto (fun d : ℝ => d) L (𝓝 0) := nhdsWithin_le_nhds
  have hp : Tendsto (fun d : ℝ => 2+d) L (𝓝 2) := by simpa using hd.const_add 2
  have hT : Tendsto T L (𝓝 0) := by
    change Tendsto (fun d : ℝ => -d/(2+d)) L (𝓝 0)
    convert hd.neg.div hp (by norm_num : (2:ℝ)≠0) using 1 <;> norm_num
  have good : ∀ᶠ d in L, d≠0 ∧ 1<2+d := (show ∀ᶠ d in L, d≠0 from self_mem_nhdsWithin).and
    (hp.eventually (Ioi_mem_nhds (by norm_num : (1:ℝ)<2)))
  have hT' : Tendsto T L (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr ⟨hT,good.mono fun d h => by
    exact div_ne_zero (neg_ne_zero.mpr h.1) (by linarith [h.2])⟩
  have H := (symmetricGammaLog_limit.comp hT').div hp (by norm_num : (2:ℝ)≠0)
  have hP : Tendsto (fun d => P d/d^2) L (𝓝 k₀) := by
    have he : π^2/6/2=k₀ := by unfold k₀; ring
    rw [he] at H
    apply H.congr'
    filter_upwards [good] with d ⟨hd,hp⟩
    change symmetricGammaLog (T d)/(T d)^2/(2+d)=P d/d^2
    dsimp only [P,T]
    field_simp [hd,show 2+d≠0 by linarith] <;> ring
  have hP₀ : Tendsto P L (𝓝 0) := by
    have h := hP.mul (hd.pow 2)
    simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero] at h
    apply h.congr'
    filter_upwards [good] with d h
    exact div_mul_cancel₀ _ (pow_ne_zero _ h.1)
  let ex := dslope Real.exp 0
  have he : ContinuousAt ex 0 := continuousAt_dslope_same.mpr (Real.hasDerivAt_exp 0).differentiableAt
  have he0 : ex 0=1 := by simp [ex,Real.deriv_exp]
  have hL := (he.tendsto.comp hP₀).mul hP
  rw [he0,one_mul] at hL
  apply hL.congr'
  filter_upwards [good] with d ⟨hd,hp⟩
  have hp0 : 0<2+d := by linarith
  have h₁ : 1+T d=2/(2+d) := by dsimp [T]; field_simp; ring
  have h₂ : 1-T d=2-2/(2+d) := by dsimp [T]; field_simp; ring
  have hg₁ : 0<Real.Gamma (2/(2+d)) := Real.Gamma_pos_of_pos (by positivity)
  have hg₂ : 0<Real.Gamma (2-2/(2+d)) := Real.Gamma_pos_of_pos (by rw [sub_pos,div_lt_iff₀ hp0]; linarith)
  have hpow : liuNorm (2+d)^(2+d)=Real.exp (P d) := by
    rw [Real.rpow_def_of_pos (liuNorm_pos hp),liuNorm,Real.log_mul hg₁.ne' hg₂.ne']
    dsimp only [P,symmetricGammaLog]; rw [h₁,h₂,mul_comm]
  have ee := sub_smul_dslope Real.exp 0 (P d)
  change _ * ex _ = _ at ee
  simp only [sub_zero,Real.exp_zero] at ee
  change ex (P d)*(P d/d^2)=_
  rw [hpow,←ee]
  ring

end Liu
