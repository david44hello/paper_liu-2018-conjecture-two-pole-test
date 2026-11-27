module

public import Liu.PolePolarization
public import Liu.OnePoleBounds

@[expose] public section

noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu

def rankSource (p c w : ℂ) : ℂ := (w-p)⁻¹*conj ((w-c)⁻¹)

def rankField (p c z : ℂ) : ℂ := -(∫ w, greenResolvent z w*rankSource p c w ∂upperArea)

theorem rankSource_decay {p c w : ℂ} (hp : p.im<0) (hc : c.im<0) (hw : 0≤w.im) :
    ‖rankSource p c w‖ ≤ (poleBound 1 p*poleBound 1 c)/(1+‖w‖)^2 := by
  have B {b : ℂ} (h : b.im<0) : ‖(w-b)⁻¹‖ ≤ poleBound 1 b/(1+‖w‖) := by
    simpa [pole,one_div] using pole_global_decay (a:=1) zero_lt_one h hw
  simp only [rankSource,norm_mul,Complex.norm_conj]
  calc
    _ ≤ poleBound 1 p/(1+‖w‖)*(poleBound 1 c/(1+‖w‖)) := mul_le_mul (B hp) (B hc) (norm_nonneg _) ((norm_nonneg _).trans (B hp))
    _ = _ := by rw [div_mul_div_comm,←sq]

theorem rankField_polar_analytic (p c : ℂ) {z : ℂ} (hz : 0≤z.im) :
    AnalyticOnNhd ℂ (fun t => rankField (polarPole p c t) (polarPole p c (conj t)) z) (polarWindow p c) := by
  let P := polarPole p c
  let U := polarWindow p c
  have hU := polar_window_open p c
  have hP : Differentiable ℂ P := (differentiable_id.mul_const _).const_add _
  have hs {t : ℂ} (ht : t∈U) : conj t∈U := ⟨ht.2,by simpa only [Complex.conj_conj] using ht.1⟩
  apply DifferentiableOn.analyticOnNhd _ hU
  apply DifferentiableOn.neg
  apply differentiableOn_local_integral upperArea hU
  · intro t
    exact (show Measurable (fun w => greenResolvent z w*rankSource (P t) (P (conj t)) w) by
      unfold greenResolvent rankSource; fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
    have hn (t : ℂ) (ht : t∈U) : w-P t≠0 := sub_ne_zero.mpr fun e => by
      have hl : (P t).im<0 := ht.1
      have hpos : 0<w.im := hw
      rw [e] at hpos; linarith
    have hF := (hP.differentiableOn.const_sub w).inv hn
    exact (hF.mul (PickChart.reflected_differentiable hU (fun _ => hs) hF)).const_mul _
  · intro t ht
    let B := fun v => poleBound 1 (P v)*poleBound 1 (P (conj v))
    have h₁ : -(P t).im ≠ 0 := neg_ne_zero.mpr (show (P t).im<0 from ht.1).ne
    have h₂ : -(P (conj t)).im ≠ 0 := neg_ne_zero.mpr (show (P (conj t)).im<0 from ht.2).ne
    have hPC := hP.continuous
    have hB : ContinuousAt B t := by unfold B poleBound; fun_prop (disch := assumption)
    let K := |B t|+1
    have hK : 0≤K := by dsimp [K]; positivity
    have he : ∀ᶠ v in 𝓝 t, B v < K := hB.eventually_lt continuousAt_const (by dsimp [K]; linarith [le_abs_self (B t)])
    obtain ⟨_,_,hi⟩ := gradientWeight_integral
    refine ⟨fun w => (2*K)*gradientWeight z w,(hi z).1.const_mul _,U∩{v | B v<K},inter_mem (hU.mem_nhds ht) he,?_⟩
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,upperArea_ae_ne z] with w hw hn
    intro v hv
    have hb := (rankSource_decay (p:=P v) (c:=P (conj v)) hv.1.1 hv.1.2 (le_of_lt hw)).trans
      (div_le_div_of_nonneg_right (le_of_lt hv.2) (sq_nonneg _))
    rw [norm_mul]
    apply (mul_le_mul (greenResolvent_bound hz hw hn.symm) hb (norm_nonneg _) (by positivity)).trans
    exact (show _ = (2*K)*(‖z-w‖⁻¹/(1+‖w‖)^2) by ring).le.trans
      (mul_le_mul_of_nonneg_left (gradientWeight_majorizes z w) (by positivity))

theorem rankField_diagonal {p z : ℂ} (hp : p.im<0) (hz : 0≤z.im) :
    field (pole 1 p) z = (Complex.I/2)*rankField p p z := by
  let b := -p.im
  have hb : 0<b := neg_pos.mpr hp
  let S := singlePick 1 p.re b zero_lt_one hb
  have he : S.value=pole 1 p := by
    rw [singlePick_value]; congr 1; dsimp [b]; apply Complex.ext <;> simp
  have hh := (S.field_integral_closed hz).2
  rw [he] at hh
  rw [hh,rankField,mul_neg,←integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
  have hn : w≠p := by intro e; have hpos : 0<w.im := hw; rw [e] at hpos; linarith
  rw [singlePole_source zero_lt_one hn,rankSource,Complex.mul_conj']
  simp [one_div,norm_inv,inv_pow]; ring

end Liu
