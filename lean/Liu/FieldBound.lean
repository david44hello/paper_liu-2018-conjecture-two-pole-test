import Liu.KernelControl
import Liu.PolarizedDefect

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate
namespace Liu

private theorem log_norm_increment {x y w : ℂ} (hx : x≠w) (hy : y≠w) :
    log ‖x-w‖ - log ‖y-w‖ ≤ ‖x-y‖*‖y-w‖⁻¹ := by
  have hp := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hq := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
  have h := log_le_sub_one_of_pos (div_pos hp hq)
  rw [log_div hp.ne' hq.ne'] at h
  apply h.trans
  rw [←div_eq_mul_inv,sub_le_iff_le_add]
  apply (div_le_iff₀ hq).mpr
  rw [add_mul,div_mul_cancel₀ _ hq.ne',one_mul]
  simpa using norm_add_le (x-y) (y-w)

theorem greenLog_difference {x y w : ℂ} (hx : x∈upper) (hy : y∈upper) (hw : w∈upper)
    (hnx : x≠w) (hny : y≠w) :
    |greenLog x w-greenLog y w| ≤ ‖x-y‖*(‖x-w‖⁻¹+‖y-w‖⁻¹) := by
  have sep (z : ℂ) (hz : z∈upper) : z≠conj w := fun he => by
    have hi := congrArg Complex.im he
    simp at hi; change 0<z.im at hz; change 0<w.im at hw; linarith
  have cmp (z : ℂ) (hz : z∈upper) (hn : z≠w) : ‖z-conj w‖⁻¹ ≤ ‖z-w‖⁻¹ :=
    inv_anti₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hn)) (distance_to_reflection_bound w z (le_of_lt hw) (le_of_lt hz))
  have xy := log_norm_increment (sep x hx) (sep y hy)
  have yx := log_norm_increment (sep y hy) (sep x hx)
  have hxy := log_norm_increment hnx hny
  have hyx := log_norm_increment hny hnx
  rw [norm_sub_rev y x] at yx hyx
  have a := mul_le_mul_of_nonneg_left (cmp x hx hnx) (norm_nonneg (x-y))
  have b := mul_le_mul_of_nonneg_left (cmp y hy hny) (norm_nonneg (x-y))
  simp only [greenLog,log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (sep x hx))) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hnx)),
    log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (sep y hy))) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hny)),mul_add]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private def cubeTail (w : ℂ) : ℝ := (1+‖w‖)^(-(3:ℝ))

def gradientWeight (z w : ℂ) : ℝ :=
  localInverse z w + 8*cubeTail (w-z) + cubeTail w

theorem gradientWeight_majorizes (z w : ℂ) :
    ‖z-w‖⁻¹/(1+‖w‖)^2 ≤ gradientWeight z w := by
  have hT (v : ℂ) : 0≤cubeTail v := rpow_nonneg (by positivity) _
  have hi : 0≤localInverse z w := indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _
  let d := ‖z-w‖
  let R := 1+‖w‖
  have hR : 1≤R := by dsimp [R]; linarith [norm_nonneg w]
  have hRp := zero_lt_one.trans_le hR
  by_cases near : w ∈ Metric.ball z 1
  · have h := div_le_self (inv_nonneg.mpr (norm_nonneg (z-w))) (by nlinarith [sq_nonneg (R-1)] : 1≤R^2)
    change d⁻¹/R^2 ≤ _
    simp only [gradientWeight,localInverse,indicator_of_mem near]
    dsimp only [d] at *
    linarith [hT (w-z),hT w]
  · have hd : 1≤d := by simpa [d,Metric.mem_ball,dist_eq_norm,norm_sub_rev w z] using near
    have hdp := zero_lt_one.trans_le hd
    have tail (v : ℂ) : cubeTail v = ((1+‖v‖)^3)⁻¹ := by simp [cubeTail,rpow_neg (by positivity : 0≤1+‖v‖)]
    by_cases small : d≤R
    · have h := div_le_div_of_nonneg_left (inv_nonneg.mpr hdp.le) (sq_pos_of_pos hdp) (pow_le_pow_left₀ hdp.le small 2)
      have hg : d⁻¹/d^2 ≤ 8*cubeTail (w-z) := by
        rw [tail,norm_sub_rev w z]
        change d⁻¹/d^2 ≤ 8*((1+d)^3)⁻¹
        have hc := pow_le_pow_left₀ (by positivity : 0≤1+d) (by linarith : 1+d≤2*d) 3
        field_simp [hdp.ne',show 1+d ≠0 by positivity]; nlinarith only [hc]
      change d⁻¹/R^2 ≤ _
      unfold gradientWeight
      linarith [hT w]
    · have hi' := inv_anti₀ hRp (le_of_not_ge small)
      have hh : d⁻¹/R^2 ≤ cubeTail w := by
        rw [tail]
        calc
          _ ≤ R⁻¹/R^2 := div_le_div_of_nonneg_right hi' (sq_nonneg _)
          _ = (R^3)⁻¹ := by field_simp [hRp.ne']
      change d⁻¹/R^2 ≤ _
      unfold gradientWeight
      linarith [hT (w-z)]

theorem gradientWeight_integral :
    ∃ A ≥ 0, ∀ z : ℂ, Integrable (gradientWeight z) upperArea ∧ (∫ w, gradientWeight z w ∂upperArea) ≤ A := by
  have hT : Integrable cubeTail volume := integrable_one_add_norm (by norm_num)
  have hT0 (w : ℂ) : 0≤cubeTail w := rpow_nonneg (by positivity) _
  have hi0 (z w : ℂ) : 0≤localInverse z w := indicator_nonneg (fun v _ => inv_nonneg.mpr (norm_nonneg _)) _
  have hA : 0≤∫ w, localInverse 0 w := integral_nonneg (fun w => hi0 0 w)
  have hB : 0≤∫ w, cubeTail w := integral_nonneg (fun w => hT0 w)
  refine ⟨(1/π)*((∫ w, localInverse 0 w)+9*∫ w, cubeTail w),by positivity,?_⟩
  intro z
  let e := Homeomorph.addRight (-z)
  have mp := measurePreserving_add_right (volume:Measure ℂ) (-z)
  have ht : Integrable (fun w => cubeTail (w-z)) volume := by
    simpa [sub_eq_add_neg,Function.comp_def] using (mp.integrable_comp_emb e.measurableEmbedding).mpr hT
  have he : (∫ w, cubeTail (w-z))=∫ w, cubeTail w := by
    simpa [sub_eq_add_neg] using mp.integral_comp e.measurableEmbedding cubeTail
  have hf : Integrable (gradientWeight z) volume := ((localInverse_integrable z).add (ht.const_mul 8)).add hT
  have ha : Integrable (gradientWeight z) area := hf.smul_measure ENNReal.ofReal_ne_top
  refine ⟨ha.restrict,(integral_mono_measure Measure.restrict_le_self (ae_of_all area (fun w => ?_)) ha).trans_eq ?_⟩
  · exact add_nonneg (add_nonneg (hi0 z w) (mul_nonneg (by norm_num) (hT0 (w-z)))) (hT0 w)
  · rw [area,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤1/π),smul_eq_mul]
    congr 1
    change (∫ w : ℂ, (localInverse z w + 8*cubeTail (w-z))+cubeTail w ∂volume) = _
    have hij : Integrable (fun a => localInverse z a+8*cubeTail (a-z)) volume := (localInverse_integrable z).add (ht.const_mul 8)
    rw [integral_add hij hT,
      integral_add (localInverse_integrable z) (ht.const_mul 8),integral_const_mul,localInverse_integral z,he]
    ring

theorem PickSum.potential_lipschitz {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ x ∈ upper, ∀ y ∈ upper, ‖potential p.value x-potential p.value y‖ ≤ C*‖x-y‖ := by
  obtain ⟨A,hA,h⟩ := gradientWeight_integral
  let K := p.derivativeBound/2
  have hK : 0≤K := by simpa [K] using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  refine ⟨2*K*A,by positivity,?_⟩
  intro x hx y hy
  obtain ⟨hi,hu⟩ := h x
  obtain ⟨hj,hv⟩ := h y
  let g := fun w => (‖x-y‖*K)*(gradientWeight x w+gradientWeight y w)
  have hg : Integrable g upperArea := (hi.add hj).const_mul _
  letI : NullSingletonClass area := ⟨fun z => by simp [area,Measure.smul_apply]⟩
  letI : NullSingletonClass upperArea := by unfold upperArea; infer_instance
  have hb : ∀ᵐ w ∂upperArea,
      ‖(greenLog x w:ℂ)*source p.value w-(greenLog y w:ℂ)*source p.value w‖ ≤ g w := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,upperArea.ae_ne x,upperArea.ae_ne y] with w hw hnx hny
    rw [←sub_mul,←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hk := greenLog_difference hx hy hw hnx.symm hny.symm
    apply (mul_le_mul hk (p.source_decay (le_of_lt hw)) (norm_nonneg _) (by positivity)).trans
    calc
      _ = (‖x-y‖*K)*(‖x-w‖⁻¹/(1+‖w‖)^2+‖y-w‖⁻¹/(1+‖w‖)^2) := by dsimp only [K]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (gradientWeight_majorizes x w) (gradientWeight_majorizes y w)) (by positivity)
  have hh := norm_integral_le_of_norm_le hg hb
  rw [integral_sub (p.potential_integrable hx) (p.potential_integrable hy)] at hh
  apply hh.trans
  simp only [g,integral_const_mul,integral_add hi hj]
  calc
    _ ≤ (‖x-y‖*K)*(A+A) := mul_le_mul_of_nonneg_left (add_le_add hu hv) (by positivity)
    _ = _ := by ring

theorem PickSum.field_bounded_upper {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ z ∈ upper, ‖field p.value z‖ ≤ C := by
  obtain ⟨B,hB,h⟩ := p.potential_lipschitz
  refine ⟨2*B,by positivity,?_⟩
  intro z hz
  have hd := norm_fderiv_le_of_lip' ℝ hB (by
    filter_upwards [upper_open.mem_nhds hz] with w hw using h w hw z hz)
  let D := fderiv ℝ (potential p.value) z
  have h1 := D.le_opNorm (1:ℂ)
  have hI := D.le_opNorm Complex.I
  change ‖D‖ ≤ B at hd
  unfold field
  rw [norm_neg]
  apply (norm_sub_le ..).trans
  simp only [norm_mul,Complex.norm_I,one_mul]
  simp only [norm_one,Complex.norm_I,mul_one] at h1 hI
  change ‖D 1‖+‖D Complex.I‖ ≤ _
  linarith

end Liu
