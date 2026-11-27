module

public import Liu.ProjectionKernel
public import Liu.KernelFar

@[expose] public section

noncomputable section
open Set MeasureTheory Metric Real
namespace Liu

theorem PickSum.residualIntegral_bound {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 1<t) (ht2 : t<2) :
    ∃ C > 0, ∀ z ∈ upper, ‖∫ w, residualIntegrand (p.power t) z w ∂upperArea‖ ≤
      C*(1+log (1+‖z‖))/(1+‖z‖)^t := by
  classical
  have ht0 := zero_lt_one.trans ht
  obtain ⟨N,hN,hnear⟩ := p.residual_near_bound ht0
  obtain ⟨D,hD,hfar⟩ := p.residual_far_bound ht0
  let A := ∫ v, localInverse 0 v
  let B := ∫ v, radialWeight t v
  have hA : 0 ≤ A := integral_nonneg (fun v => indicator_nonneg (fun u _ => inv_nonneg.mpr (norm_nonneg _)) _)
  have hB : 0 ≤ B := integral_nonneg fun v => by unfold radialWeight; positivity
  have hC : 0 ≤ (1/π)*(N*A+D*B) := by positivity
  refine ⟨1+(1/π)*(N*A+D*B),by linarith,?_⟩
  intro z hz
  let R := 1+‖z‖
  let ζ := R⁻¹ • z
  let f := residualIntegrand (p.power t) z
  let q := (1+log R)/(R^t*R^2)
  have hr : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
  have hRp := zero_lt_one.trans_le hr
  have hl := log_nonneg hr
  have hq : 0 < q := by dsimp [q]; positivity
  have hj : Integrable (localInverse ζ) volume := localInverse_integrable ζ
  have hb := radialWeight_integrable ht ht2
  let g := fun v : ℂ => q*(N*localInverse ζ v + D*radialWeight t v)
  have hg : Integrable g volume := ((hj.const_mul N).add (hb.const_mul D)).const_mul q
  have hgi : ∫ v, g v = q*(N*A+D*B) := by
    simp only [g,integral_const_mul,integral_add (hj.const_mul N) (hb.const_mul D),localInverse_integral ζ,A,B]
  have hn (v : ℂ) : ‖R • v-z‖ = R*‖v-ζ‖ := by
    have h : R • v-z = R • (v-ζ) := by rw [smul_sub,show R • ζ=z by simp [ζ,smul_smul,hRp.ne']]
    rw [h,norm_smul,Real.norm_eq_abs,abs_of_pos hRp]
  have point (v : ℂ) : ‖upper.indicator (fun y => f (R • y)) v‖ ≤ g v := by
    have hi : 0 ≤ localInverse ζ v := indicator_nonneg (fun w _ => inv_nonneg.mpr (norm_nonneg _)) _
    have hw : 0 ≤ radialWeight t v := by unfold radialWeight; positivity
    by_cases hv : v ∈ upper
    · rw [indicator_of_mem hv]
      have hscaled : R • v ∈ upper := by change 0<(R • v).im; simpa [Complex.real_smul,hRp] using (show 0 < v.im from hv)
      by_cases near : ‖v-ζ‖ ≤ 1/2
      · have hnear' : ‖R • v-z‖ ≤ R/2 := by rw [hn]; nlinarith [mul_le_mul_of_nonneg_left near hRp.le]
        have hbound := hnear z (R • v) hz hscaled hnear'
        have hmem : v ∈ ball ζ 1 := by change dist v ζ < 1; rw [dist_eq_norm]; linarith
        have hlocal : localInverse ζ v = ‖v-ζ‖⁻¹ := by simp [localInverse,hmem,norm_sub_rev ζ v]
        rw [hn] at hbound
        have h0 : N/(R^t*R)*(R*‖v-ζ‖)⁻¹ = N/(R^t*R^2)*‖v-ζ‖⁻¹ := by rw [mul_inv_rev]; ring
        change _ ≤ N/(R^t*R)*(R*‖v-ζ‖)⁻¹ at hbound
        rw [h0,←hlocal] at hbound
        apply hbound.trans
        dsimp only [g,q]
        have hsmall : N/(R^t*R^2)*localInverse ζ v ≤
            (1+log R)/(R^t*R^2)*(N*localInverse ζ v) := by
          have hpos : 0≤N*localInverse ζ v := mul_nonneg hN.le hi
          field_simp [hRp.ne',(rpow_pos_of_pos hRp t).ne']
          <;> nlinarith [mul_nonneg hl hpos]
        exact hsmall.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hD.le hw)) hq.le)
      · have hfar' : R/2 ≤ ‖R • v-z‖ := by rw [hn]; nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge near) hRp.le]
        have hbound := hfar z v hz hv hfar'
        change _ ≤ D*(1+log R)/(R^t*R^2)*radialWeight t v at hbound
        apply hbound.trans
        have h' : D*(1+log R)/(R^t*R^2)*radialWeight t v = q*(D*radialWeight t v) := by dsimp [q]; ring
        rw [h']
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg hN.le hi)) hq.le
    · rw [indicator_of_notMem hv,norm_zero]
      dsimp [g]; positivity
  have hbound := norm_integral_le_of_norm_le hg (ae_of_all _ point)
  rw [hgi,integral_indicator upper_open.measurableSet] at hbound
  have hpre (v : ℂ) : v ∈ upper ↔ R • v ∈ upper := by
    change 0<v.im ↔ 0<(R • v).im; simp [Complex.real_smul,hRp]
  have hscale := area_integral_dilate f hRp upper_open.measurableSet upper_open.measurableSet hpre
  have hscale' : (∫ w in upper, f w ∂area) = (R^2) • ∫ v in upper, f (R • v) ∂area := by
    rw [hscale,smul_smul,mul_inv_cancel₀ (pow_ne_zero 2 hRp.ne'),one_smul]
  change ‖∫ w in upper, f w ∂area‖ ≤ _
  rw [hscale',norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  unfold area
  rw [Measure.restrict_smul,integral_smul_measure,ENNReal.toReal_ofReal (by positivity),
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/π)]
  calc
    _ ≤ R^2*((1/π)*(q*(N*A+D*B))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound (by positivity)) (sq_nonneg _)
    _ = ((1/π)*(N*A+D*B))*(1+log R)/R^t := by dsimp [q]; field_simp [hRp.ne'] <;> ring
    _ ≤ _ := by change _ ≤ (1+_)*(1+log R)/R^t; gcongr; linarith

theorem PickSum.projected_domination {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 1<t) (ht2 : t<2) :
    ∃ G : ℂ → ℂ, ∃ hG : MemLp G 2 upperArea,
      hG.toLp G = asL2 (logInput (p.power t))-project (asL2 (logInput (p.power t))) ∧
      ∃ C > 0, ∀ z ∈ upper, ‖G z‖ ≤ C*‖p.power t z‖*(1+|log ‖p.power t z‖|) := by
  obtain ⟨G,hG,he,hi⟩ := critical_residual_integral (p.power_memLp_two ht)
    (p.power_holomorphic t) (p.log_power_memLp_two ht)
  obtain ⟨C,hC,hbound⟩ := p.residualIntegral_bound ht ht2
  obtain ⟨c,hc,hscale⟩ := p.power_two_sided (zero_lt_one.trans ht).le
  obtain ⟨B,hB,hlog⟩ := p.log_power_growth (zero_lt_one.trans ht)
  refine ⟨G,hG,he,C*(1+B)/c,by positivity,?_⟩
  intro z hz
  rw [hi z hz]
  apply (hbound z hz).trans
  let R := 1+‖z‖
  let L := |log ‖p.power t z‖|
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
  have hℓ := log_nonneg hR
  have hL : 0≤L := abs_nonneg _
  have hlg := (hlog z (le_of_lt hz)).2
  change t*log R ≤ B+L at hlg
  have hh : 1+log R ≤ (1+B)*(1+L) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.le) hℓ,mul_nonneg hB.le hL]
  have hlow := (hscale z (le_of_lt hz)).1
  have hfac : (1/R^t) ≤ ‖p.power t z‖/c := by
    apply (le_div_iff₀ hc).mpr
    convert hlow using 1 <;> ring
  calc
    _ = C*(1+log R)*(1/R^t) := by dsimp [R]; ring
    _ ≤ (C*((1+B)*(1+L)))*(‖p.power t z‖/c) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hh hC.le) hfac (by positivity) (by positivity)
    _ = _ := by dsimp [L]; ring

end Liu
