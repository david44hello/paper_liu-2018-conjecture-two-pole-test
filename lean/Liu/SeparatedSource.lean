import Liu.SeparatedNodes
import Liu.LocalParameterIntegral

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu.PickChart

def value (P : PickChart) (w z : ℂ) : ℂ := -P.valueFactor w z/(z+Complex.I)

def rho (P : PickChart) (w z : ℂ) : ℂ :=
  P.valueFactor w z * conj (P.derivativeRatio (conj w) z)/((‖z+Complex.I‖^2:ℝ):ℂ)

def trace (P : PickChart) (w : ℂ) (x : ℝ) : ℂ :=
  ∫ z, ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*P.rho w z ∂upperArea

theorem reflected_differentiable {U : Set ℂ} (hU : IsOpen U)
    (hs : ∀ w ∈ U, conj w ∈ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fun w => conj (f (conj w))) U := by
  intro w hw
  have h := (hf.differentiableAt (hU.mem_nhds (hs w hw))).conj_conj
  simpa only [Complex.conj_conj,Function.comp_def] using h.differentiableWithinAt (s:=U)

theorem Regular.factors_diff {P : PickChart} {U : Set ℂ} (h : P.Regular U) {z : ℂ} (hz : 0≤z.im) :
    DifferentiableOn ℂ (fun w => P.valueFactor w z) U ∧
    DifferentiableOn ℂ (fun w => P.derivativeRatio w z) U := by
  have factor (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) :
      DifferentiableOn ℂ (fun w => nodeFactor (f w) z) U := (hf.const_sub z).div_const _
  have A := factor P.left h.left
  have B := factor P.right h.right
  have N := factor P.zeroNode h.zero_diff
  have Ai := A.inv fun w hw => (nodeFactor_bounds (h.left_below w hw) hz).1
  have Bi := B.inv fun w hw => (nodeFactor_bounds (h.right_below w hw) hz).1
  have Ni := N.inv fun w hw => (nodeFactor_bounds (h.zero_below w hw) hz).1
  exact ⟨(N.mul Ai).mul Bi,(((h.mass.mul Ai).mul B).mul Ni).add
    ((((h.mass.const_sub 1).mul Bi).mul A).mul Ni)⟩

theorem Regular.rho_diff {P : PickChart} {U : Set ℂ} (h : P.Regular U) {z : ℂ} (hz : 0≤z.im) :
    DifferentiableOn ℂ (fun w => P.rho w z) U :=
  ((h.factors_diff hz).1.mul (reflected_differentiable h.isOpen h.reflection (h.factors_diff hz).2)).div_const _

theorem Regular.local_bounds {P : PickChart} {U : Set ℂ} (h : P.Regular U) {c : ℂ} (hc : c∈U) :
    ∃ K : ℝ, 0≤K ∧ ∃ V ∈ 𝓝 c, ∀ w ∈ V, w∈U ∧ P.size w ≤ K ∧ P.size (conj w) ≤ K := by
  let K := max (P.size c) (P.size (conj c)) + 1
  have h₁ : P.size c<K := by dsimp [K]; linarith [le_max_left (P.size c) (P.size (conj c))]
  have h₂ : P.size (conj c)<K := by dsimp [K]; linarith [le_max_right (P.size c) (P.size (conj c))]
  have l := (h.size_continuous hc).eventually_lt (continuousAt_const (y:=K)) h₁
  have r := ((h.size_continuous (h.reflection c hc)).comp (by fun_prop : ContinuousAt (conj : ℂ → ℂ) c)).eventually_lt
    (continuousAt_const (y:=K)) h₂
  have hK : 0≤K := by have : 1≤P.size c := le_max_left ..; linarith
  refine ⟨K,hK,{w | w∈U ∧ P.size w≤K ∧ P.size (conj w)≤K},?_,fun _ hw => hw⟩
  filter_upwards [h.isOpen.mem_nhds hc,l,r] with w hw hl hr using ⟨hw,hl.le,hr.le⟩

theorem Regular.rho_bound {P : PickChart} {U : Set ℂ} (h : P.Regular U) {w z : ℂ}
    (hw : w∈U) (hz : 0≤z.im) {K : ℝ} (hl : P.size w≤K) (hr : P.size (conj w)≤K) :
    ‖P.rho w z‖ ≤ (2*K^7)/‖z+Complex.I‖^2 := by
  have a := (factors_bounded h hw hz).1
  have b := (factors_bounded h (h.reflection w hw) hz).2
  have hl₀ : 0≤P.size w := (show (0:ℝ)≤1 by norm_num).trans (le_max_left ..)
  have hr₀ : 0≤P.size (conj w) := (show (0:ℝ)≤1 by norm_num).trans (le_max_left ..)
  simp only [rho,norm_div,norm_mul,Complex.norm_conj,Complex.norm_of_nonneg (sq_nonneg _)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ K^3*(2*K^4) := mul_le_mul (a.trans (pow_le_pow_left₀ hl₀ hl _))
      (b.trans (by gcongr)) (norm_nonneg _) (pow_nonneg (hl₀.trans hl) _)
    _ = _ := by ring

private theorem density_bound {P : PickChart} {U : Set ℂ} (h : P.Regular U) {w z : ℂ}
    (hw : w∈U) (hz : 0≤z.im) {K : ℝ} (hl : P.size w≤K) (hr : P.size (conj w)≤K) (x : ℝ) :
    ‖((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*P.rho w z‖ ≤ (2*K^7)*isolatedDensity 1 (-Complex.I) x z := by
  have hp : 0≤z.im/‖z-(x:ℂ)‖^2 := by positivity
  rw [norm_mul,Complex.norm_of_nonneg hp,isolatedDensity,sub_neg_eq_add]
  exact (mul_le_mul_of_nonneg_left (h.rho_bound hw hz hl hr) hp).trans_eq (by ring)

theorem Regular.trace_hasDeriv {P : PickChart} {U : Set ℂ} (h : P.Regular U) {c : ℂ} (hc : c∈U) (x : ℝ) :
    HasDerivAt (fun w => P.trace w x)
      (∫ z, deriv (fun w => ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*P.rho w z) c ∂upperArea) c := by
  obtain ⟨K,_,V,hV,hK⟩ := h.local_bounds hc
  refine hasDerivAt_local_integral upperArea h.isOpen hc ?_ ?_
    (M:=fun z => (2*K^7)*isolatedDensity 1 (-Complex.I) x z) ?_ hV ?_
  · intro w
    exact (show Measurable (fun z : ℂ => ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*P.rho w z) by
      unfold rho valueFactor derivativeRatio nodeFactor; fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    exact (h.rho_diff (le_of_lt hz)).const_mul _
  · exact (isolatedDensity_integral zero_lt_one (by simp : (-Complex.I).im<0) x).1.const_mul _
  · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    intro w hw
    exact density_bound h (hK w hw).1 (le_of_lt hz) (hK w hw).2.1 (hK w hw).2.2 x

theorem Regular.trace_diff {P : PickChart} {U : Set ℂ} (h : P.Regular U) (x : ℝ) :
    DifferentiableOn ℂ (fun w => P.trace w x) U :=
  fun _ hc => (h.trace_hasDeriv hc x).differentiableAt.differentiableWithinAt

theorem Regular.trace_bound {P : PickChart} {U : Set ℂ} (h : P.Regular U) {w : ℂ} (hw : w∈U)
    {K : ℝ} (hl : P.size w≤K) (hr : P.size (conj w)≤K) (x : ℝ) :
    ‖P.trace w x‖ ≤ (2*K^7)*isolatedTrace 0 1 x := by
  obtain ⟨hi,he⟩ := isolatedDensity_integral zero_lt_one (by simp : (-Complex.I).im<0) x
  apply (norm_integral_le_of_norm_le (hi.const_mul (2*K^7)) ?_).trans_eq
  · rw [integral_const_mul,he]; simp
  · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    exact density_bound h hw (le_of_lt hz) hl hr x

end Liu.PickChart
