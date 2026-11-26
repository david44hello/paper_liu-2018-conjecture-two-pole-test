import Liu.FieldIntegral
import Liu.RadialSource
import Liu.GreenRadialWeights

noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate
namespace Liu

def radialSource (m : ℝ) (w : ℂ) : ℂ := Complex.I*((m/(2*‖w‖^2):ℝ):ℂ)

/-- One bound covers the cubic error at infinity and the model's inverse-square
singularity at the origin. The origin is outside the open half-plane. -/
theorem PickSum.source_radial_comparison {n : ℕ} (p : PickSum n) :
    ∃ K ≥ 0, ∀ w ∈ upper, ‖source p.value w-radialSource p.mass w‖ ≤ K/(‖w‖^2*(1+‖w‖)) := by
  obtain ⟨A,hA,hfar⟩ := p.source_far_model
  let B := p.derivativeBound/2
  have hB : 0≤B := by simpa [B] using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  have hm := p.mass_pos
  refine ⟨2*(A+B+p.mass/2),by positivity,?_⟩
  intro w hw
  let r := ‖w‖
  have hr : 0<r := (show 0<w.im from hw).trans_le (Complex.im_le_norm w)
  by_cases hh : 1<r
  · apply (hfar w (le_of_lt hw) hh).trans
    change A/r^3 ≤ _
    apply (div_le_div_iff₀ (pow_pos hr 3) (by positivity)).mpr
    change A*(r^2*(1+r)) ≤ _*r^3
    have h := mul_le_mul_of_nonneg_left (by linarith : 1+r≤2*r) (mul_nonneg hA (sq_nonneg r))
    nlinarith only [h,mul_nonneg hB (pow_nonneg hr.le 3),mul_nonneg hm.le (pow_nonneg hr.le 3)]
  · have hle := le_of_not_gt hh
    have hρ : ‖source p.value w‖ ≤ B := (p.source_decay (le_of_lt hw)).trans
      (div_le_self hB (by nlinarith [norm_nonneg w,sq_nonneg ‖w‖]))
    have hr' : ‖radialSource p.mass w‖ = (p.mass/2)/r^2 := by
      unfold radialSource; rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0≤p.mass/(2*‖w‖^2))]
      dsimp [r]; ring
    apply (norm_sub_le ..).trans
    rw [hr']
    apply (add_le_add hρ le_rfl).trans
    have hs : r^2≤1 := by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hle)]
    have hb : B ≤ B/r^2 := (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by nlinarith [mul_le_mul_of_nonneg_left hs hB])
    calc
      _ ≤ B/r^2+(p.mass/2)/r^2 := add_le_add hb le_rfl
      _ = (B+p.mass/2)/r^2 := (add_div ..).symm
      _ ≤ _ := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hr) (by positivity)).mpr
        change _ ≤ _*r^2
        have h := mul_le_mul_of_nonneg_left (by linarith : 1+r≤2) (by positivity : 0≤(B+p.mass/2)*r^2)
        nlinarith only [h,mul_nonneg hA (sq_nonneg r)]

/-- The reflected derivative of a remainder of size 1/(r²(1+r)) has the
logarithmic radial gradient decay, uniformly in the observation angle. -/
theorem greenResolvent_radial_error {ρ : ℂ → ℂ} (hm : Measurable ρ) {K : ℝ} (hK : 0≤K)
    (hs : ∀ w ∈ upper, ‖ρ w‖ ≤ K/(‖w‖^2*(1+‖w‖))) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → 1<‖z‖ → Integrable (fun w => greenResolvent z w*ρ w) upperArea ∧
      (∫ w, ‖greenResolvent z w*ρ w‖ ∂upperArea) ≤ C*(1+log ‖z‖)/‖z‖^2 := by
  let A := ∫ w, localInverse 0 w
  have hA : 0≤A := integral_nonneg fun w => indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _
  have hl := log_nonneg (by norm_num : (1:ℝ)≤3)
  let C := 16*K*(1/π)*A + 8*K*(1+log 3)+K
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro z hz hr
  let R := ‖z‖
  have hR : 0<R := zero_lt_one.trans hr
  let L := fun w => localInverse (R⁻¹ • z) (R⁻¹ • w)
  have hLV : Integrable L volume := (localInverse_integrable _).comp_smul (inv_ne_zero hR.ne')
  have hLA : Integrable L area := hLV.smul_measure ENNReal.ofReal_ne_top
  have hL0 (w : ℂ) : 0≤L w := indicator_nonneg (fun _ _ => by positivity) _
  have hLI : (∫ w, L w ∂upperArea) ≤ (1/π)*(R^2*A) := by
    apply (integral_mono_measure Measure.restrict_le_self (ae_of_all area hL0) hLA).trans_eq
    rw [area,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤1/π),smul_eq_mul]
    congr 1
    change (∫ w, localInverse (R⁻¹ • z) (R⁻¹ • w)) = _
    simpa only [inv_pow,inv_inv] using scaled_localInverse_integral (R⁻¹ • z) R⁻¹ (inv_pos.mpr hR)
  have hL : Integrable L upperArea := hLA.restrict
  obtain ⟨hM,hMI⟩ := momentDisc_integral (show 0<2*R by positivity)
  obtain ⟨hF,hFI⟩ := exteriorFourth_integral (show 0<2*R by positivity)
  let g := fun w => (16*K/R^4)*L w+(8*K/R^2)*momentDisc (2*R) w+(4*K)*exteriorFourth (2*R) w
  have hN := hL.const_mul (16*K/R^4)
  have hmid := hM.const_mul (8*K/R^2)
  have hfar := hF.const_mul (4*K)
  have hg : Integrable g upperArea := (hN.add hmid).add hfar
  have hpoint : ∀ᵐ w ∂upperArea, ‖greenResolvent z w*ρ w‖ ≤ g w := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,upperArea_ae_ne z] with w hw hn
    let r := ‖w‖
    let d := ‖z-w‖
    have hp : 0<r := (show 0<w.im from hw).trans_le (Complex.im_le_norm w)
    have hd : 0<d := norm_pos_iff.mpr (sub_ne_zero.mpr hn.symm)
    have hb : ‖ρ w‖ ≤ K/r^3 := (hs w hw).trans (div_le_div_of_nonneg_left hK (pow_pos hp 3) (by
      change r^3 ≤ r^2*(1+r); nlinarith only [sq_nonneg r]))
    have hnl : 0≤(16*K/R^4)*L w := by have := hL0 w; positivity
    have hnm : 0≤(8*K/R^2)*momentDisc (2*R) w := by unfold momentDisc; split <;> positivity
    have hnf : 0≤(4*K)*exteriorFourth (2*R) w := by unfold exteriorFourth; split <;> positivity
    rw [norm_mul]
    by_cases near : d<R/2
    · have ht := norm_sub_le_norm_sub_add_norm_sub z w 0
      simp only [sub_zero] at ht
      change R≤d+r at ht
      have hrr := pow_le_pow_left₀ (half_pos hR).le (by linarith : R/2≤r) 3
      have hs' : ‖ρ w‖ ≤ 8*K/R^3 := hb.trans (by
        apply (div_le_div_iff₀ (pow_pos hp _) (pow_pos hR _)).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hrr hK])
      have hk := mul_le_mul (greenResolvent_bound hz hw hn.symm) hs' (norm_nonneg _) (by positivity)
      have eqn : 2*‖z-w‖⁻¹*(8*K/R^3)=(16*K/R^4)*L w := by
        rw [show L w=R*‖z-w‖⁻¹ from scaled_inverse_near hR near]; field_simp [hR.ne'] <;> ring
      dsimp only [g]; linarith only [hk,eqn,hnm,hnf]
    · by_cases outer : 2*R<r
      · have ht := norm_sub_le_norm_sub_add_norm_sub w z 0
        simp only [sub_zero,norm_sub_rev w z] at ht
        change r≤d+R at ht
        have hi : d⁻¹ ≤ 2/r := by rw [inv_eq_one_div]; apply (div_le_div_iff₀ hd hp).mpr; linarith
        have hk' : ‖greenResolvent z w‖ ≤ 4/r := (greenResolvent_bound hz hw hn.symm).trans (by
          change 2*d⁻¹ ≤ 4/r; calc
            _ ≤ 2*(2/r) := by linarith
            _ = _ := by ring)
        apply (mul_le_mul hk' hb (norm_nonneg _) (by positivity)).trans
        have eqn : (4/r)*(K/r^3) = (4*K)*exteriorFourth (2*R) w := by
          rw [exteriorFourth,if_pos outer]; change _ = (4*K)*(r^4)⁻¹; field_simp [hp.ne'] <;> ring
        dsimp only [g]; linarith only [eqn,hnl,hnm]
      · have hsq := pow_le_pow_left₀ (half_pos hR).le (le_of_not_gt near) 2
        have hk : ‖greenResolvent z w‖ ≤ 8*r/R^2 := (greenResolvent_moment_bound hz hw hn.symm).trans (by
          apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos hR)).mpr
          have him : w.im≤r := Complex.im_le_norm _
          nlinarith only [mul_le_mul_of_nonneg_left hsq hp.le,mul_le_mul_of_nonneg_right him (sq_nonneg R)])
        apply (mul_le_mul hk (hs w hw) (norm_nonneg _) (by positivity)).trans
        have eqn : 8*r/R^2*(K/(‖w‖^2*(1+‖w‖)))=(8*K/R^2)*momentDisc (2*R) w := by
          rw [momentDisc,if_pos (le_of_not_gt outer)]
          change _*(K/(r^2*(1+r)))=(8*K/R^2)*(r⁻¹/(1+r))
          field_simp [hp.ne',hR.ne',show 1+r≠0 by positivity] <;> ring
        dsimp only [g]; linarith only [eqn,hnl,hnf]
  have hm' : Measurable (fun w => greenResolvent z w*ρ w) := by unfold greenResolvent; fun_prop
  have hI := hg.mono' hm'.aestronglyMeasurable hpoint
  refine ⟨hI,?_⟩
  have hb := integral_mono_ae hI.norm hg hpoint
  have hnm : Integrable (fun w => (16*K/R^4)*L w+(8*K/R^2)*momentDisc (2*R) w) upperArea := hN.add hmid
  simp only [g,integral_add hnm hfar,integral_add hN hmid,integral_const_mul,hMI,hFI] at hb
  apply hb.trans
  have hlog := log_nonneg hr.le
  have hln : log (1+2*R)≤log 3+log R := by
    rw [←log_mul (by norm_num) hR.ne']
    exact log_le_log (by positivity) (by change 1+2*R≤3*R; change 1<R at hr; linarith)
  have hn' := mul_le_mul_of_nonneg_left hLI (show 0≤16*K/R^4 by positivity)
  have hm' := mul_le_mul_of_nonneg_left hln (show 0≤8*K/R^2 by positivity)
  apply (add_le_add (add_le_add hn' hm') le_rfl).trans
  change _ ≤ C*(1+log R)/R^2
  dsimp [C]
  field_simp [hR.ne',pi_ne_zero]
  nlinarith [mul_nonneg (show 0≤16*K*A by positivity) hlog,
    mul_nonneg (show 0≤8*K*π*log 3 by positivity) hlog,
    mul_nonneg (show 0≤K*π by positivity) hlog,mul_nonneg hK pi_pos.le]

end Liu
