module

public import Liu.CanonicalField
public import Liu.GreenPairing

@[expose] public section

noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate Topology
namespace Liu

private def originWeight (t : ℝ) (v : ℂ) : ℝ :=
  (ball (0:ℂ) 1).indicator (fun w => ‖w‖^(-(1+t))) v

private theorem originWeight_integrable {t : ℝ} (ht : t<1) : Integrable (originWeight t) volume := by
  apply (integrable_indicator_iff isOpen_ball.measurableSet).mpr
  apply integrableOn_ball_of_norm_le_rpow (C:=1) (α:=1+t) (by simp) (by simp; linarith)
  · filter_upwards with w
    rw [Real.norm_eq_abs,abs_of_nonneg (rpow_nonneg (norm_nonneg _) _),one_mul]
  · exact (show Measurable (fun w : ℂ => ‖w‖^(-(1+t))) by fun_prop).aestronglyMeasurable

private theorem unit_resolvent_majorant {t : ℝ} (ht : 0<t) {z v : ℂ} (hz : 0≤z.im) (hz1 : ‖z‖=1) (hv : v∈upper)
    (hne : z≠v) :
    ‖greenResolvent z v‖*‖v‖^(-(2+t)) ≤
      8*originWeight t v + (2*2^(2+t))*localInverse z v + (2*3^(2+t))*(1+‖v‖)^(-(2+t)) := by
  let r := ‖v‖
  let d := ‖z-v‖
  have hr : 0<r := (show 0<v.im from hv).trans_le (Complex.im_le_norm v)
  have hq : 0<2+t := by linarith
  have hT : 0≤originWeight t v := indicator_nonneg (fun u _ => rpow_nonneg (norm_nonneg _) _) _
  have hL : 0≤localInverse z v := indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) _
  have hF : 0≤(1+‖v‖)^(-(2+t)) := rpow_nonneg (by positivity) _
  have hN := greenResolvent_bound hz hv hne
  have hM := greenResolvent_moment_bound hz hv hne
  by_cases small : r<1/2
  · have hd : 1/2≤d := by
      have h := norm_sub_le_norm_sub_add_norm_sub z v 0
      simp only [sub_zero,hz1] at h; change 1≤d+r at h; linarith
    have hd0 : 0<d := lt_of_lt_of_le (by norm_num) hd
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) hd 2
    have hk : ‖greenResolvent z v‖ ≤ 8*r := hM.trans (by
      apply (div_le_iff₀ (sq_pos_of_pos hd0)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hsq hr.le,Complex.im_le_norm v])
    have hand : originWeight t v = r^(-(1+t)) := indicator_of_mem (show v∈ball (0:ℂ) 1 by simpa using (by linarith : ‖v‖<1)) _
    apply (mul_le_mul_of_nonneg_right hk (rpow_nonneg (norm_nonneg v) _)).trans
    have he : 8*r*‖v‖^(-(2+t))=8*originWeight t v := by
      rw [hand,show -(1+t)=1+ -(2+t) by ring,rpow_add hr,rpow_one]; ring
    rw [he]
    linarith [mul_nonneg (by positivity : 0≤(2:ℝ)*2^(2+t)) hL,mul_nonneg (by positivity : 0≤(2:ℝ)*3^(2+t)) hF]
  · have hhalf : (1/2:ℝ)≤r := le_of_not_gt small
    by_cases near : v∈ball z 1
    · have hs : r^(-(2+t))≤(2:ℝ)^(2+t) := by
        rw [rpow_neg hr.le,←inv_rpow hr.le]
        exact rpow_le_rpow (inv_nonneg.mpr hr.le) ((inv_le_comm₀ hr (by norm_num : (0:ℝ)<2)).mpr (by simpa using hhalf)) hq.le
      have hloc : localInverse z v=d⁻¹ := indicator_of_mem near _
      have hh := mul_le_mul hN hs (rpow_nonneg hr.le _) (by positivity)
      change ‖greenResolvent z v‖*r^(-(2+t)) ≤ _
      rw [hloc]
      change ‖greenResolvent z v‖*r^(-(2+t)) ≤ (2*d⁻¹)*2^(2+t) at hh
      linarith [mul_nonneg (by positivity : 0≤(2:ℝ)*3^(2+t)) hF]
    · have hd : 1≤d := by simpa [d,mem_ball,dist_eq_norm,norm_sub_rev v z] using near
      have hk : ‖greenResolvent z v‖≤2 := hN.trans (by
        have hi := inv_anti₀ zero_lt_one hd
        change 2*d⁻¹≤2; simpa only [inv_one,mul_one] using mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤2))
      have hscale := rpow_le_rpow (by positivity : 0≤1+r) (by linarith : 1+r≤3*r) hq.le
      rw [mul_rpow (by norm_num) hr.le] at hscale
      have hs : r^(-(2+t))≤(3:ℝ)^(2+t)*(1+r)^(-(2+t)) := by
        rw [rpow_neg hr.le,rpow_neg (by positivity : 0≤1+r),←div_eq_mul_inv,←one_div]
        apply (div_le_div_iff₀ (rpow_pos_of_pos hr _) (rpow_pos_of_pos (by positivity) _)).mpr
        simpa only [one_mul] using hscale
      apply (mul_le_mul hk hs (rpow_nonneg hr.le _) (by norm_num)).trans
      have h0 : 2*(3^(2+t)*(1+r)^(-(2+t)))=(2*3^(2+t))*(1+‖v‖)^(-(2+t)) := by dsimp only [r]; ring
      rw [h0]
      exact le_add_of_nonneg_left (by positivity)

theorem greenResolvent_supercritical_decay {t K : ℝ} (ht : 0<t) (ht1 : t<1) (hK : 0≤K) {f : ℂ → ℂ}
    (hs : ∀ w ∈ upper, ‖f w‖ ≤ K/(1+‖w‖)^(2+t)) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → z≠0 →
      (∫ w, ‖greenResolvent z w*f w‖ ∂upperArea) ≤ C/‖z‖^(1+t) := by
  let F := fun w : ℂ => (1+‖w‖)^(-(2+t))
  have hF : Integrable F volume := integrable_one_add_norm (μ:=(volume:Measure ℂ)) (r:=2+t) (by simp; linarith)
  have hT := originWeight_integrable ht1
  let B := 8*(∫ v, originWeight t v)+(2*2^(2+t))*(∫ v, localInverse 0 v)+(2*3^(2+t))*(∫ v, F v)
  have hB : 0≤B := by
    have h1 : 0≤∫ v, originWeight t v := integral_nonneg fun v => indicator_nonneg (fun _ _ => rpow_nonneg (norm_nonneg _) _) _
    have h2 : 0≤∫ v, localInverse 0 v := integral_nonneg fun v => indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) _
    have h3 : 0≤∫ v, F v := integral_nonneg fun v => rpow_nonneg (by positivity) _
    dsimp only [B]; positivity
  refine ⟨K*(1/π)*B,by positivity,?_⟩
  intro z hz hn
  let R := ‖z‖
  have hR : 0<R := norm_pos_iff.mpr hn
  let ζ := R⁻¹ • z
  have hζ : ‖ζ‖=1 := by change ‖R⁻¹ • z‖=1; rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]; exact inv_mul_cancel₀ hR.ne'
  have hy : 0≤ζ.im := by dsimp [ζ]; simp [Complex.real_smul]; positivity
  have hsc (v : ℂ) : greenResolvent z (R • v) = (R:ℂ)⁻¹*greenResolvent ζ v := by
    rw [show z=R • ζ by simp [ζ,smul_smul,hR.ne']]
    simp only [greenResolvent,Complex.real_smul,map_mul,Complex.conj_ofReal,←mul_sub,mul_inv_rev]; ring
  let M := fun v => 8*originWeight t v+(2*2^(2+t))*localInverse ζ v+(2*3^(2+t))*F v
  have hL := localInverse_integrable ζ
  have hm₁ : Integrable (fun v => 8*originWeight t v+(2*2^(2+t))*localInverse ζ v) volume :=
    (hT.const_mul 8).add (hL.const_mul _)
  have hM : Integrable M volume := hm₁.add (hF.const_mul _)
  have hMI : ∫ v, M v=B := by
    simp only [M,B,integral_add hm₁ (hF.const_mul _),integral_add (hT.const_mul _) (hL.const_mul _),integral_const_mul,
      localInverse_integral ζ]
  have hM0 (v : ℂ) : 0≤M v := by
    have hO : 0≤originWeight t v := indicator_nonneg (fun _ _ => rpow_nonneg (norm_nonneg _) _) _
    have hL0 : 0≤localInverse ζ v := indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) _
    have hF0 : 0≤F v := rpow_nonneg (by positivity) _
    dsimp only [M]; positivity
  let D := K/R^(3+t)
  have hD : 0≤D := by dsimp only [D]; positivity
  have hMA : Integrable M area := hM.smul_measure ENNReal.ofReal_ne_top
  have hMU : (∫ v, M v ∂upperArea) ≤ (1/π)*B := by
    apply (integral_mono_measure Measure.restrict_le_self (ae_of_all area hM0) hMA).trans_eq
    rw [area,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤1/π),smul_eq_mul,hMI]
  let g := fun w => ‖greenResolvent z w*f w‖
  have point : ∀ᵐ v ∂upperArea, ‖g (R • v)‖ ≤ D*M v := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,upperArea_ae_ne ζ] with v hv hne
    have hvp : 0<‖v‖ := (show 0<v.im from hv).trans_le (Complex.im_le_norm _)
    have hV : R • v∈upper := by change 0<(R • v).im; simpa [Complex.real_smul,hR] using (show 0<v.im from hv)
    have hnorm : ‖R • v‖=R*‖v‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    have hs' : ‖f (R • v)‖ ≤ (K/R^(2+t))*‖v‖^(-(2+t)) := by
      apply (hs _ hV).trans
      rw [hnorm]
      apply (div_le_div_of_nonneg_left hK (rpow_pos_of_pos (mul_pos hR hvp) _) (rpow_le_rpow (by positivity) (by linarith : R*‖v‖≤1+R*‖v‖) (by linarith))).trans_eq
      rw [mul_rpow hR.le hvp.le,rpow_neg hvp.le]; ring
    change ‖‖greenResolvent z (R • v)*f (R • v)‖‖ ≤ _
    rw [norm_norm,norm_mul,hsc,norm_mul,norm_inv,Complex.norm_of_nonneg hR.le]
    apply (mul_le_mul_of_nonneg_left hs' (by positivity)).trans
    have eqn : R⁻¹*‖greenResolvent ζ v‖*(K/R^(2+t)*‖v‖^(-(2+t))) =
        D*(‖greenResolvent ζ v‖*‖v‖^(-(2+t))) := by
      have hpwr : R^(3+t)=R*R^(2+t) := by rw [show 3+t=1+(2+t) by ring,rpow_add hR,rpow_one]
      dsimp only [D]; rw [hpwr]; ring
    rw [eqn]
    exact mul_le_mul_of_nonneg_left (unit_resolvent_majorant ht hy hζ hv hne.symm) hD
  have hb : (∫ v, g (R • v) ∂upperArea) ≤ D*((1/π)*B) := by
    have hh := norm_integral_le_of_norm_le ((show Integrable M upperArea from hMA.restrict).const_mul D) point
    rw [Real.norm_eq_abs,integral_const_mul] at hh
    exact ((le_abs_self _).trans hh).trans (mul_le_mul_of_nonneg_left hMU hD)
  have hpre (v : ℂ) : v∈upper ↔ R • v∈upper := by change 0<v.im ↔ 0<(R • v).im; simp [Complex.real_smul,hR]
  have hscale := area_integral_dilate g hR upper_open.measurableSet upper_open.measurableSet hpre
  change (∫ v, g (R • v) ∂upperArea) = (R^2)⁻¹*(∫ w, g w ∂upperArea) at hscale
  rw [hscale] at hb
  change (∫ w, g w ∂upperArea) ≤ _/R^(1+t)
  calc
    _ = R^2*((R^2)⁻¹*∫ w, g w ∂upperArea) := by field_simp [hR.ne']
    _ ≤ R^2*(D*((1/π)*B)) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by dsimp only [D]; rw [show 3+t=2+(1+t) by ring,rpow_add hR,rpow_ofNat]; field_simp [hR.ne'] <;> ring

end Liu
