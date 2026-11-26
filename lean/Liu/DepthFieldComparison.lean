import Liu.SmallFirstOrder
import Liu.DepthTraceContinuity

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped ComplexConjugate Topology
namespace Liu

theorem isWitness_depthTranslate {W : ℂ → ℂ} (hW : isWitness W) {t : ℝ} (ht : 0≤t) :
    isWitness (depthTranslate W t) := by
  let v := fun z : ℂ => z+(t:ℂ)*Complex.I
  have hv (z : ℂ) : (v z).im=z.im+t := by simp [v]
  have hU : MapsTo v upper upper := by intro z hz; change 0<(v z).im; rw [hv]; linarith [show 0<z.im from hz]
  have hC : MapsTo v {w : ℂ | 0≤w.im} {w : ℂ | 0≤w.im} := by
    intro z hz; change 0≤(v z).im; rw [hv]; linarith [show 0≤z.im from hz]
  have hd : Differentiable ℂ v := by dsimp [v]; fun_prop
  refine ⟨hW.1.comp hd.differentiableOn hU,hW.2.1.comp hd.continuous.continuousOn hC,?_⟩
  obtain ⟨A,hA,T,hT,ha⟩ := hW.2.2
  have hlog := log_nonneg (by norm_num : (1:ℝ)≤2)
  refine ⟨A*(1+log 2),by positivity,max 1 (max t T),lt_of_lt_of_le zero_lt_one (le_max_left ..),?_⟩
  intro z hz hr
  let r := ‖z‖
  have hr1 : 1≤r := (le_max_left 1 _).trans hr
  have hrp := zero_lt_one.trans_le hr1
  have htr : t≤r := (le_max_left t T).trans ((le_max_right 1 _).trans hr)
  have hrz : r≤‖v z‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    dsimp only [r,v]; simp [Complex.sq_norm,Complex.normSq_apply]; nlinarith [mul_nonneg hz ht,sq_nonneg t]
  have hvp := hrp.trans_le hrz
  have hvu : ‖v z‖≤2*r := (norm_add_le z ((t:ℂ)*Complex.I)).trans (by rw [norm_mul,Complex.norm_of_nonneg ht,Complex.norm_I,mul_one]; change r+t≤2*r; linarith)
  have h := ha (v z) (hC hz) ((le_max_right t T).trans ((le_max_right 1 _).trans (hr.trans hrz)))
  have hl := log_le_log hvp hvu
  rw [log_mul (by norm_num) hrp.ne'] at hl
  apply h.trans
  have hrlog := log_nonneg hr1
  apply div_le_div₀ (by positivity : 0≤A*(1+log 2)*(1+log r)) _ hrp hrz
  nlinarith only [mul_le_mul_of_nonneg_left hl hA.le,mul_nonneg (mul_nonneg hA.le hlog) (log_nonneg hr1)]

/-- The energy gained by reoptimizing the witness after translating the poles
is controlled by the squared L² increment of the earlier physical field. -/
theorem PickSum.depth_witness_energy_le {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0≤t)
    (hΔ : MemLp (fun z => depthTranslate (field p.value) t z-field p.value z) 2 upperArea) :
    let q := p.deeper t ht
    let W := depthTranslate (optimalWitness p.value) t
    let G := witnessDifference q.value W
    energy G≤energy (fun z => depthTranslate (field p.value) t z-field p.value z) := by
  let q := p.deeper t ht
  let W := depthTranslate (optimalWitness p.value) t
  let G := witnessDifference q.value W
  let d := fun z => depthTranslate (field p.value) t z-field p.value z
  have hW := isWitness_depthTranslate p.optimalWitness_isWitness ht
  have hg := (q.witness_identity.2 W hW).1
  have hp := cross_witness_orthogonality p q hW q.optimalWitness_isWitness
  have hq := cross_witness_orthogonality q q hW q.optimalWitness_isWitness
  let K := fun z => (field q.value z-field p.value z)*conj (G z)
  have hK : Integrable K upperArea := by
    simpa only [K,G,witnessDifference,Pi.sub_def,sub_mul] using hq.1.sub hp.1
  have hkint : (∫ z, K z ∂upperArea)=0 := by
    dsimp only [K]; simp_rw [sub_mul]
    erw [integral_sub hq.1 hp.1,hq.2,hp.2,sub_zero]
  have hΔ' := (memLp_two_iff_integrable_sq_norm hΔ.aestronglyMeasurable).mp hΔ
  have hg' := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hle : (∫ z, ‖G z‖^2-2*(K z).re ∂upperArea)≤∫ z, ‖d z‖^2 ∂upperArea := by
    apply integral_mono_ae (hg'.sub ((Complex.reCLM.integrable_comp hK).const_mul 2)) hΔ'
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    let v := z+(t:ℂ)*Complex.I
    have hv : 0≤v.im := by dsimp [v]; simp; linarith [show 0<z.im from hz]
    have hn₁ : p.value v≠0 := fun h => by have H := p.value_im_pos hv; simp [h] at H
    have hn₂ : q.value z≠0 := fun h => by have H := q.value_im_pos (le_of_lt hz); simp [h] at H
    have hS : q.value z=p.value v := congrFun (p.deeper_value ht) z
    have hG : G z=field q.value z-field p.value v := by
      rw [field_eq_witness_product hn₁,field_eq_witness_product hn₂]
      change q.value z*(W z-optimalWitness q.value z)=_
      rw [←hS]; change q.value z*(optimalWitness p.value v-optimalWitness q.value z)=_; ring
    let b := field q.value z-field p.value z
    have he : d z=b-G z := by rw [hG]; dsimp [b,d,depthTranslate,v]; ring
    have hid : ‖b-G z‖^2=‖b‖^2+‖G z‖^2-2*(b*conj (G z)).re := by
      simp [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re]; ring
    change ‖G z‖^2-2*(K z).re ≤ ‖d z‖^2
    rw [he,hid]; change ‖G z‖^2-2*(b*conj (G z)).re≤_; linarith [sq_nonneg ‖b‖]
  have hzero : (∫ z, (K z).re ∂upperArea)=0 := (integral_re hK).trans (by rw [hkint]; rfl)
  erw [integral_sub hg' ((Complex.reCLM.integrable_comp hK).const_mul 2),integral_const_mul,hzero,mul_zero,sub_zero] at hle
  change energy G≤energy d
  erw [energy_eq_integral hg,energy_eq_integral hΔ]; exact hle

end Liu
