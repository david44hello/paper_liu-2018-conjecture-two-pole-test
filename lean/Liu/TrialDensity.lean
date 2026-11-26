import Liu.TrialBound

noncomputable section
open Set Real Complex Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace Liu

def trialWeight (a η : ℝ) : ℝ := a^(2-η)+a^(2+η)

theorem trialWeight_bound {a η d : ℝ} (ha : 0<a) (hd : |d|≤η) :
    a^(2+d) ≤ trialWeight a η := by
  unfold trialWeight
  rcases le_total a 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge ha h (by linarith [(abs_le.mp hd).1])).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg ha.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le h (by linarith [(abs_le.mp hd).2])).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _))

private theorem weight_deriv {a : ℝ} (ha : 0<a) (t : ℝ) :
    HasDerivAt (fun s : ℝ => a^(2+s)) (Real.log a*a^(2+t)) t := by
  simpa using ((hasDerivAt_id t).const_add 2).const_rpow ha

theorem trialWeight_slope_bound {a η d : ℝ} (ha : 0<a) (hd : |d|≤η) :
    |(a^(2+d)-a^2)/d| ≤ |Real.log a| *trialWeight a η := by
  have hη : 0≤η := (abs_nonneg d).trans hd
  have hb (t : ℝ) (ht : t∈Icc (-η) η) : ‖Real.log a*a^(2+t)‖ ≤ |Real.log a| *trialWeight a η := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg ha.le _)]
    exact mul_le_mul_of_nonneg_left (trialWeight_bound ha (abs_le.mpr ht)) (abs_nonneg _)
  have h := (convex_Icc (-η) η).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (weight_deriv ha t).hasDerivWithinAt) hb
    (show (0:ℝ)∈Icc (-η) η from ⟨by linarith,hη⟩) (abs_le.mp hd)
  simp only [add_zero,Real.rpow_two,sub_zero,Real.norm_eq_abs] at h
  by_cases h₀ : d=0
  · simp [h₀,trialWeight]; positivity
  rw [abs_div,div_le_iff₀ (abs_pos.mpr h₀)]
  exact h

/-- The linear compensation integrates to zero for the orthogonal trial vector. -/
def trialDensity (f g : ℂ) (d : ℝ) :=
  (‖f-(d:ℂ)*g‖^(2+d)-‖f‖^(2+d)+2*d*(g*conj f).re)/d^2

private theorem trial_cross {f : ℂ} (hf : f≠0) (g : ℂ) :
    (g*conj f).re=‖f‖^2*(g/f).re := by
  have h : g*conj f = ((‖f‖^2:ℝ):ℂ)*(g/f) := by
    push_cast
    rw [←Complex.mul_conj']
    field_simp
  rw [h,Complex.re_ofReal_mul]

theorem trialDensity_factor {f : ℂ} (hf : f≠0) (g : ℂ) {d : ℝ} (hd : d≠0) :
    trialDensity f g d =
      ‖f‖^(2+d)*trialFactor (g/f) d -
      2*(g/f).re*((‖f‖^(2+d)-‖f‖^2)/d) := by
  have eq : f-(d:ℂ)*g=f*(1-(d:ℂ)*(g/f)) := by field_simp <;> ring
  rw [trialDensity,trialFactor,trial_cross hf,eq,norm_mul,Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  field_simp
  <;> ring

theorem trialDensity_limit {f : ℂ} (hf : f≠0) (g : ℂ) :
    Tendsto (trialDensity f g) (𝓝[≠] 0)
      (𝓝 (‖g‖^2-(g*conj f).re-2*Real.log ‖f‖*(g*conj f).re)) := by
  have ha := norm_pos_iff.mpr hf
  have h := weight_deriv ha 0
  simp only [add_zero,Real.rpow_two] at h
  have hs : Tendsto (fun d : ℝ => slope (fun t : ℝ => ‖f‖^(2+t)) 0 d) (𝓝[≠] 0) (𝓝 (Real.log ‖f‖*‖f‖^2)) := hasDerivAt_iff_tendsto_slope.mp h
  simp only [slope_def_field,add_zero,Real.rpow_two,sub_zero] at hs
  have ht := (h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul (trialFactor_limit (g/f))
  have H := ht.sub (hs.const_mul (2*(g/f).re))
  simp only [add_zero,Real.rpow_two] at H
  have eq : ‖f‖^2*‖g/f‖^2=‖g‖^2 := by rw [norm_div,div_pow]; field_simp
  rw [trial_cross hf,show ‖g‖^2-‖f‖^2*(g/f).re-2*Real.log ‖f‖*(‖f‖^2*(g/f).re)=
    ‖f‖^2*(‖g/f‖^2-(g/f).re)-2*(g/f).re*(Real.log ‖f‖*‖f‖^2) by rw [mul_sub,eq]; ring]
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with d (hd : d≠0)
  exact (trialDensity_factor hf g hd).symm

theorem trialDensity_bound {f g : ℂ} {d η C : ℝ} (hf : f≠0)
    (hC : 0≤C) (hg : ‖g/f‖≤C*(1+|Real.log ‖f‖|)) (hd : |d|≤η) (hη : η≤1) :
    |trialDensity f g d| ≤ (100*(1+C)^3+2*C)*
      (trialWeight ‖f‖ η*(1+|Real.log ‖f‖|)^5) := by
  have ha := norm_pos_iff.mpr hf
  let L := 1+|Real.log ‖f‖|
  have hL : 1≤L := by dsimp [L]; linarith [abs_nonneg (Real.log ‖f‖)]
  have hL₀ : 0≤L := by linarith
  have hW : 0≤trialWeight ‖f‖ η := add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ha.le _)
  by_cases hd₀ : d=0
  · simp only [hd₀,trialDensity,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,div_zero,abs_zero]
    positivity
  rw [trialDensity_factor hf g hd₀]
  apply (abs_sub ..).trans
  simp only [abs_mul,abs_of_nonneg (Real.rpow_nonneg ha.le _),abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h₁ : 1+‖g/f‖ ≤ (1+C)*L := by change ‖g/f‖≤C*L at hg; linarith
  have h₃ := pow_le_pow_left₀ (by positivity : 0≤1+‖g/f‖) h₁ 3
  rw [mul_pow] at h₃
  have h₅ : L^3≤L^5 := pow_le_pow_right₀ hL (by decide)
  have hA := mul_le_mul (trialWeight_bound ha hd) (trialFactor_bound (g/f) (hd.trans hη)) (abs_nonneg _) hW
  have hB := mul_le_mul (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hg) (by norm_num : (0:ℝ)≤2))
    (trialWeight_slope_bound ha hd) (abs_nonneg _) (by positivity)
  have hab : |Real.log ‖f‖|≤L := by dsimp [L]; linarith
  have hP : L*|Real.log ‖f‖|≤L^5 := (mul_le_mul_of_nonneg_left hab hL₀).trans
    (by simpa [sq] using (pow_le_pow_right₀ hL (by decide : 2≤5)))
  apply (add_le_add hA hB).trans
  change _ ≤ (100*(1+C)^3+2*C)*(trialWeight ‖f‖ η*L^5)
  calc
    _ ≤ trialWeight ‖f‖ η*(100*((1+C)^3*L^5)) + (2*C*trialWeight ‖f‖ η)*(L*|Real.log ‖f‖|) := by
      apply add_le_add
      · gcongr; exact h₃.trans (mul_le_mul_of_nonneg_left h₅ (by positivity))
      · dsimp only [L]; apply le_of_eq; ring
    _ ≤ trialWeight ‖f‖ η*(100*((1+C)^3*L^5)) + (2*C*trialWeight ‖f‖ η)*L^5 := by gcongr
    _ = _ := by ring

end Liu
