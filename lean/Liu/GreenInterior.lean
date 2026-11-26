import Liu.GreenDifferential

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate
namespace Liu

def scaledWeight (r : ℝ) (x w : ℂ) := localInverse (r⁻¹ • x) (r⁻¹ • w)

theorem scaledWeight_estimate {r : ℝ} (hr : 0<r) (x : ℂ) :
    Integrable (scaledWeight r x) upperArea ∧
    (∫ w, scaledWeight r x w ∂upperArea) ≤ (1/π)*(r^2*∫ w, localInverse 0 w) := by
  have hv : Integrable (scaledWeight r x) volume := (localInverse_integrable _).comp_smul (inv_ne_zero hr.ne')
  have ha : Integrable (scaledWeight r x) area := hv.smul_measure ENNReal.ofReal_ne_top
  refine ⟨ha.restrict,(integral_mono_measure Measure.restrict_le_self (ae_of_all area (fun w =>
    indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _)) ha).trans_eq ?_⟩
  rw [area,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤1/π),smul_eq_mul]
  congr 1
  change (∫ w, localInverse (r⁻¹ • x) (r⁻¹ • w)) = _
  simpa only [inv_pow,inv_inv] using scaled_localInverse_integral (r⁻¹ • x) r⁻¹ (inv_pos.mpr hr)

/-- A uniform first-order approximation for the potential of a quadratically
decaying source. A square-root radius around the singularity separates the
integrable local logarithmic difference from the quadratic Taylor error. -/
theorem reflectedPotential_remainder {ρ : ℂ → ℂ} (hm : Measurable ρ) {K : ℝ} (hK : 0≤K)
    (hb : ∀ w ∈ upper, ‖ρ w‖≤K/(1+‖w‖)^2)
    (hi : ∀ z ∈ upper, Integrable (fun w => (greenLog z w:ℂ)*ρ w) upperArea) :
    ∃ C ≥ 0, ∀ z ∈ upper, ∀ x ∈ upper, ‖x-z‖≤1/4 →
      ‖reflectedPotential ρ x-reflectedPotential ρ z-greenDifferential ρ z (x-z)‖ ≤
        C*‖x-z‖*sqrt ‖x-z‖ := by
  obtain ⟨B,hB,hgrad⟩ := gradientWeight_integral
  let A := ∫ w, localInverse 0 w
  have hA : 0≤A := integral_nonneg (fun w => indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _)
  refine ⟨16*K*(1/π)*A+2*K*B,by positivity,?_⟩
  intro z hz x hx hdist
  by_cases eq : x=z
  · simp [eq]
  let l := ‖x-z‖
  let δ := sqrt l
  have hl : 0<l := norm_pos_iff.mpr (sub_ne_zero.mpr eq)
  have hp : 0<δ := sqrt_pos.mpr hl
  have hδ : δ^2=l := sq_sqrt hl.le
  have hthin : l≤δ/2 := by
    have hs : δ≤1/2 := by change l≤1/4 at hdist; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs hp.le]
  let r := 4*δ
  have hr : 0<r := by dsimp [r]; positivity
  let near := fun w : ℂ => (l*K/r)*(scaledWeight r x w+3*scaledWeight r z w)
  let far := fun w : ℂ => (2*l^2*K/δ)*gradientWeight z w
  obtain ⟨hix,hux⟩ := scaledWeight_estimate hr x
  obtain ⟨hiz,huz⟩ := scaledWeight_estimate hr z
  have hn : Integrable near upperArea := (hix.add (hiz.const_mul 3)).const_mul _
  have hf : Integrable far upperArea := (hgrad z).1.const_mul _
  let F := fun w : ℂ => (greenLog x w:ℂ)*ρ w-(greenLog z w:ℂ)*ρ w-
    (((((x-z)*greenResolvent z w).re):ℝ):ℂ)*ρ w
  have eqint : (∫ w, F w ∂upperArea) =
      reflectedPotential ρ x-reflectedPotential ρ z-greenDifferential ρ z (x-z) := by
    rw [greenDifferential_apply hm hK hb (le_of_lt hz)]
    have hdif : Integrable (fun w => (greenLog x w:ℂ)*ρ w-(greenLog z w:ℂ)*ρ w) upperArea := (hi x hx).sub (hi z hz)
    simp only [F,integral_sub hdif (greenDifferential_integrable_apply hm hK hb (le_of_lt hz) _),
      integral_sub (hi x hx) (hi z hz),reflectedPotential]
  have hbnd : ∀ᵐ w ∂upperArea, ‖F w‖ ≤ near w+far w := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,upperArea_ae_ne x,upperArea_ae_ne z] with w hw hwx hwz
    have hli (v : ℂ) : 0 ≤ scaledWeight r v w := indicator_nonneg (fun u _ => inv_nonneg.mpr (norm_nonneg _)) _
    have hn0 : 0≤near w := by have := hli z; have := hli x; dsimp [near]; positivity
    have hg0 : 0≤gradientWeight z w := (by positivity : 0≤‖z-w‖⁻¹/(1+‖w‖)^2).trans (gradientWeight_majorizes z w)
    have hf0 : 0≤far w := by dsimp [far]; positivity
    dsimp only [F]
    rw [←sub_mul,←sub_mul,←Complex.ofReal_sub,←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    by_cases close : ‖z-w‖<δ
    · apply le_trans _ (le_add_of_nonneg_right hf0)
      have nx : ‖x-w‖<r/2 := by
        have h := norm_sub_le_norm_sub_add_norm_sub x z w
        change ‖x-w‖≤l+‖z-w‖ at h; dsimp [r]; linarith
      have nz : ‖z-w‖<r/2 := by dsimp [r]; linarith
      have hs := (hb w hw).trans (div_le_self hK (by nlinarith [norm_nonneg w,sq_nonneg ‖w‖]))
      apply (mul_le_mul (greenLog_remainder_near hz hx hw hwz.symm hwx.symm) hs (norm_nonneg _) (by positivity)).trans_eq
      simp only [near,scaledWeight,scaled_inverse_near hr nx,scaled_inverse_near hr nz]
      dsimp only [l]; field_simp [hr.ne'] <;> ring
    · apply le_trans _ (le_add_of_nonneg_left hn0)
      have hd : 0<‖z-w‖ := hp.trans_le (le_of_not_gt close)
      have hsm : ‖x-z‖ ≤ ‖z-w‖/2 := hthin.trans (by linarith [le_of_not_gt close])
      apply (mul_le_mul (greenLog_remainder_far hz hx hw hwz.symm hwx.symm hsm) (hb w hw)
        (norm_nonneg _) (by positivity)).trans
      have hdiv := inv_anti₀ hp (le_of_not_gt close)
      have hmult : (2*l^2*K)*(‖z-w‖⁻¹) ≤ (2*l^2*K)*δ⁻¹ := mul_le_mul_of_nonneg_left hdiv (by positivity)
      calc
        _ = ((2*l^2*K)*‖z-w‖⁻¹)*(‖z-w‖⁻¹/(1+‖w‖)^2) := by dsimp only [l]; simp only [div_pow,div_eq_mul_inv,inv_pow]; ring
        _ ≤ ((2*l^2*K)*δ⁻¹)*gradientWeight z w := mul_le_mul hmult (gradientWeight_majorizes z w) (by positivity) (by positivity)
        _ = far w := by rfl
  have hnorm := norm_integral_le_of_norm_le (hn.add hf) hbnd
  simp only [Pi.add_apply] at hnorm
  rw [eqint,integral_add hn hf] at hnorm
  simp only [near,far,integral_const_mul,integral_add hix (hiz.const_mul 3)] at hnorm
  apply hnorm.trans
  have nbd := mul_le_mul_of_nonneg_left (add_le_add hux (mul_le_mul_of_nonneg_left huz (by norm_num : (0:ℝ)≤3)))
    (show 0≤l*K/r by positivity)
  have fbd := mul_le_mul_of_nonneg_left (hgrad z).2 (show 0≤2*l^2*K/δ by positivity)
  apply (add_le_add nbd fbd).trans_eq
  change (l*K/r)*((1/π)*(r^2*A)+3*((1/π)*(r^2*A)))+(2*l^2*K/δ)*B = _*l*δ
  dsimp only [r]
  rw [←hδ]
  field_simp [hp.ne',pi_ne_zero] <;> ring

theorem reflectedPotential_hasFDerivAt {ρ : ℂ → ℂ} (hm : Measurable ρ) {K : ℝ} (hK : 0≤K)
    (hb : ∀ w ∈ upper, ‖ρ w‖≤K/(1+‖w‖)^2)
    (hi : ∀ z ∈ upper, Integrable (fun w => (greenLog z w:ℂ)*ρ w) upperArea)
    {z : ℂ} (hz : z∈upper) :
    HasFDerivAt (reflectedPotential ρ) (greenDifferential ρ z) z := by
  obtain ⟨C,hC,h⟩ := reflectedPotential_remainder hm hK hb hi
  rw [hasFDerivAt_iff_tendsto]
  have hn : Tendsto (fun x : ℂ => ‖x-z‖) (𝓝 z) (𝓝 0) := by
    simpa using ((continuous_id.sub (continuous_const (y:=z))).norm.tendsto z)
  apply squeeze_zero' (Eventually.of_forall fun _ => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)) _ (by
    simpa using (continuous_sqrt.continuousAt.tendsto.comp hn).const_mul C)
  filter_upwards [upper_open.mem_nhds hz,hn.eventually_lt_const (by norm_num : (0:ℝ)<1/4)] with x hx hs
  by_cases he : x=z
  · simp [he]
  have hp := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  apply (mul_le_mul_of_nonneg_left (h z hz x hx hs.le) (inv_nonneg.mpr hp.le)).trans_eq
  field_simp [hp.ne']

end Liu
