module

public import Liu.ContourNeighborhood

@[expose] public section

noncomputable section
open Set MeasureTheory Filter Metric Real Complex
open scoped Topology
namespace Liu

set_option maxHeartbeats 700000 in
theorem WindowFamily.contour_dominated {U} (W : WindowFamily U) (γ : RealContour) :
    DominatedFamily 1 (W.pathDomain γ) (fun w x => W.H w (γ.path x)*deriv γ.path x) := by
  have ho := W.pathDomain_open γ
  refine ⟨fun w => ?_,fun x w hw => ?_,?_⟩
  · have term (s : Bool) (p q : ℂ) : Measurable (tailTerm s p q) := by
      change Measurable (fun z : ℂ => tailTerm s p q z)
      cases s <;> unfold tailTerm sideLog <;> simp only [Bool.not_true,Bool.not_false,Bool.false_eq_true,if_false,if_true]
      all_goals unfold lowerNodeLog upperNodeLog; fun_prop
    have P (p : ℂ) : Measurable (tailPole p) := by change Measurable (fun z => -(z-p)⁻¹); fun_prop
    have side (s : Bool) (A B : Fin 3 → ℂ) (a b : ℂ) : Measurable (tailSide s A B a b) := by
      change Measurable (fun z => tailSide s A B a b z)
      unfold tailSide tailSingle tailCross; fun_prop
    have H : Measurable (W.H w) := by
      change Measurable (fun z => totalDensity (W.L w) (W.Q w) (W.mass₁ w) (W.mass₂ w) z)
      unfold totalDensity; fun_prop
    exact ((H.comp γ.continuous.measurable).mul (measurable_deriv γ.path)).aestronglyMeasurable
  · have H := W.joint_diff hw.1 (hw.2 x)
    have g : DifferentiableAt ℂ (fun t : ℂ => (t,γ.path x)) w := by fun_prop
    exact ((H.comp w g).mul_const (deriv γ.path x)).differentiableWithinAt
  · intro c hc
    obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hc)
    let K := closedBall c (r/2)
    have hK : IsCompact K := isCompact_closedBall ..
    have hk : K⊆W.pathDomain γ := (closedBall_subset_ball (half_lt_self hr)).trans hrU
    obtain ⟨B,hB,hb⟩ := W.shape_bound hK (fun w hw => (hk hw).1)
    obtain ⟨T,hT,ht⟩ := γ.tail_with_deriv
    let R := max T (10^18+4*B+1)
    have hX : (10:ℝ)^18≤R := (show (10:ℝ)^18≤10^18+4*B+1 by linarith).trans (le_max_right ..)
    have hR : 0≤R := by linarith
    let J := Icc (-R) R
    have hJ : IsCompact J := isCompact_Icc
    have Hj : ContinuousOn (fun k : ℂ × ℝ => W.H k.1 (γ.path k.2)) (K ×ˢ J) := by
      intro k hmem
      have p := W.joint_diff (hk hmem.1).1 ((hk hmem.1).2 k.2)
      have g : ContinuousAt (fun u : ℂ × ℝ => (u.1,γ.path u.2)) k := continuous_fst.continuousAt.prodMk
        (γ.continuous.continuousAt.comp continuous_snd.continuousAt)
      exact (ContinuousAt.comp (g:=fun v : ℂ × ℂ => W.H v.1 v.2) (f:=fun u : ℂ × ℝ => (u.1,γ.path u.2)) p.continuousAt g).continuousWithinAt
    obtain ⟨M,hM⟩ := (hK.prod hJ).exists_bound_of_continuousOn Hj
    let A := 144*B^2*(5+π+B)^2+16*k₀*B^2
    have hk₀ : 0≤k₀ := by unfold k₀; positivity
    have hA : 0≤A := by dsimp [A]; positivity
    have hd := (complex_ac_fundamental (γ.ac (-R) R)).2.1
    have hi : IntegrableOn (fun x => |M| * ‖deriv γ.path x‖) J :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -R≤R)).mp hd).norm.const_mul _
    have hh := (hi.integrable_indicator measurableSet_Icc).add (contourWeight_integrable.const_mul A)
    refine ⟨fun x => J.indicator (fun y => |M| * ‖deriv γ.path y‖) x + A*contourWeight x,memLp_one_iff_integrable.mpr hh,?_⟩
    filter_upwards [show K∈𝓝 c from closedBall_mem_nhds c (half_pos hr)] with w hw x
    by_cases hx : x∈J
    · rw [indicator_of_mem hx,norm_mul]
      have hm : ‖W.H w (γ.path x)‖≤|M| := (hM (w,x) ⟨hw,hx⟩).trans (le_abs_self M)
      exact (mul_le_mul_of_nonneg_right hm (norm_nonneg _)).trans (le_add_of_nonneg_right (mul_nonneg hA (by unfold contourWeight; positivity)))
    · have hxx : R≤|x| := le_of_lt (lt_of_not_ge fun e => hx (abs_le.mp e))
      obtain ⟨he,he'⟩ := ht x ((le_max_left ..).trans hxx)
      rw [indicator_of_notMem hx,zero_add,he,he',mul_one]
      have hbw := hb w hw
      have hi (k : ℝ) (h : k≤B) : 4*k<R := (show 4*k<10^18+4*B+1 by linarith).trans_le (le_max_right ..)
      exact full_contour_majorant hX hxx (W.L w) (W.Q w) _ _ (fun j => hi _ (hbw.2.1 j))
        (fun j => hi _ (hbw.2.2.1 j)) hbw.2.2.2 hbw.1

theorem WindowFamily.analytic_contour {U} (W : WindowFamily U) (γ : RealContour) :
    AnalyticOnNhd ℂ (fun w => γ.integral (W.H w)) (W.pathDomain γ) :=
  (show DifferentiableOn ℂ (fun w => γ.integral (W.H w)) (W.pathDomain γ) from
    fun _ hw => ((W.contour_dominated γ).integral_hasDeriv (W.pathDomain_open γ) hw).differentiableAt.differentiableWithinAt).analyticOnNhd (W.pathDomain_open γ)

/-- Independence for all locally absolutely continuous admissible paths.
The common tail is removed using limits of actual absolutely convergent integrals. -/
theorem WindowFamily.contour_independent {U} (W : WindowFamily U) {w : ℂ} (hw : w∈U) (γ η : RealContour)
    (hg : γ.admissible (W.L w) (W.Q w)) (he : η.admissible (W.L w) (W.Q w)) :
    γ.integral (W.H w)=η.integral (W.H w) := by
  obtain ⟨ho,H⟩ := offCuts_primitives (W.L w) (W.Q w)
  have d : DifferentiableOn ℂ (W.H w) (offCuts (W.L w) (W.Q w)) := by
    intro z hz
    exact ((W.joint_diff hw hz).comp z (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (w,z)) z)).differentiableWithinAt
  obtain ⟨g,dg⟩ := H _ d
  have hγ := (W.contour_dominated γ).integrable (show w∈W.pathDomain γ from ⟨hw,hg⟩)
  have hη := (W.contour_dominated η).integrable (show w∈W.pathDomain η from ⟨hw,he⟩)
  have L := intervalIntegral_tendsto_integral hγ tendsto_neg_atTop_atBot (tendsto_id (α:=ℝ))
  have R := intervalIntegral_tendsto_integral hη tendsto_neg_atTop_atBot (tendsto_id (α:=ℝ))
  obtain ⟨A,hA,ha⟩ := γ.tail
  obtain ⟨B,hB,hb⟩ := η.tail
  apply tendsto_nhds_unique L (R.congr' ?_)
  filter_upwards [eventually_ge_atTop (max A B)] with t ht
  have htA := (le_max_left ..).trans ht
  have htB := (le_max_right ..).trans ht
  have hpos := hA.trans_le htA
  have u := (analytic_contour_FTC ho dg (η.ac (-t) t) (fun x _ => he x)).2
  have v := (analytic_contour_FTC ho dg (γ.ac (-t) t) (fun x _ => hg x)).2
  change (∫ x in -t..t,W.H w (η.path x)*deriv η.path x)=(∫ x in -t..t,W.H w (γ.path x)*deriv γ.path x)
  rw [u,v,ha t (by simpa [abs_of_pos hpos] using htA),hb t (by simpa [abs_of_pos hpos] using htB),
    ha (-t) (by simpa [abs_of_pos hpos] using htA),hb (-t) (by simpa [abs_of_pos hpos] using htB)]

end Liu
