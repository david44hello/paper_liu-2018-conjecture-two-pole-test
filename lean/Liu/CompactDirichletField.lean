import Liu.DirichletGreenIdentity
import Liu.FieldComparison

noncomputable section
open Set MeasureTheory Complex Real Filter
open scoped ContDiff Topology
namespace Liu

theorem compact_weight_bound {V : ℂ → ℂ} (hV : ContinuousOn V closedUpper) (hc : HasCompactSupport V)
    (a : ℝ) : ∃ C≥0, ∀ z∈closedUpper, ‖V z‖≤C/(1+‖z‖)^a := by
  have hcl : IsClosed closedUpper := isClosed_le continuous_const Complex.continuous_im
  have hi := hc.isCompact.inter_right hcl
  have hw : Continuous (fun z : ℂ => (1+‖z‖)^a) := continuous_iff_continuousAt.mpr fun z => ((continuous_norm.const_add 1).continuousAt.rpow_const (Or.inl (by positivity : 1+‖z‖≠0)))
  obtain ⟨M,hM⟩ := hi.exists_bound_of_continuousOn ((hV.norm.mul hw.continuousOn).mono inter_subset_right)
  refine ⟨|M|,abs_nonneg _,fun z hz => ?_⟩
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr
  by_cases hv : z∈tsupport V
  · exact (le_abs_self _).trans ((hM z ⟨hv,hz⟩).trans (le_abs_self M))
  · simp [image_eq_zero_of_notMem_tsupport hv]

theorem compact_dirichlet_field {V : ℂ → ℂ} (h : ContDiffOn ℝ ∞ V closedUpper) (hc : HasCompactSupport V)
    (hb : ∀ x : ℝ, V x=0) {z : ℂ} (hz : z∈closedUpper) :
    dirField V z=(1/2:ℂ)*(∫ w, greenResolvent z w*dirLap V w ∂upperArea) := by
  let W := dirField V
  let ρ := upper.indicator (fun w => -(dirLap V w)/2)
  have hin : upper⊆closedUpper := fun w hw => (show 0<w.im from hw).le
  have hρ (w : ℂ) (hw : w∈upper) : ρ w= -(dirLap V w)/2 := indicator_of_mem hw _
  have cmp : HasCompactSupport (dirLap V) := (dirPart_compact (dirPart_compact hc 1) 1).add (dirPart_compact (dirPart_compact hc I) I)
  have cmpW : HasCompactSupport W := by
    have hI : HasCompactSupport ((fun _ : ℂ => I)*dirPart I V) := (dirPart_compact hc I).mul_left
    exact ((dirPart_compact hc 1).sub hI).neg
  have dρ : DifferentiableOn ℝ ρ upper := by
    apply (((dirLap_smooth h).neg.div_const (2:ℂ)).differentiableOn (by simp) |>.mono hin).congr
    exact hρ
  classical
  have hmeas : Measurable ρ := ((dirLap_smooth h).neg.div_const (2:ℂ)).continuousOn.mono hin
    |>.measurable_piecewise (continuousOn_const (c:=(0:ℂ))) upper_open.measurableSet
  have src : SupercriticalSource ρ (1/2) := by
    obtain ⟨C,hC,hb⟩ := compact_weight_bound (dirLap_smooth h).continuousOn cmp (2+1/2)
    refine ⟨by norm_num,by norm_num,hmeas,C,hC,fun w hw => ?_⟩
    rw [hρ w hw,norm_div,norm_neg,Complex.norm_ofNat]
    exact (div_le_self (norm_nonneg _) (by norm_num)).trans (hb w (hin hw))
  obtain ⟨B,hB,hW⟩ := compact_weight_bound (dirField_smooth h).continuousOn cmpW (1+1/2)
  have hWm := memLp_two_of_power_bound (by norm_num : (0:ℝ)<1/2)
    (((dirField_smooth h).continuousOn.mono hin).aestronglyMeasurable upper_open.measurableSet)
    (fun w hw => hW w (hin hw))
  obtain ⟨A,hA,hV⟩ := compact_weight_bound h.continuousOn hc 0
  have proj := dirichlet_field_projection_zero h.continuousOn
    (fun w hw => ((h w (hin hw)).contDiffAt (closedUpper_nhds hw)).differentiableAt (by simp) |>.hasFDerivAt)
    (F:=W) (by intro w hw; simp only [W,dirField,dirPart_inside _ _ hw]) hb hA
    (fun w hw => by simpa only [Real.rpow_zero,div_one] using hV w hw) hWm
  have eq := src.identify_field dρ hWm (((dirField_smooth h).differentiableOn (by simp)).mono hin)
    (fun w hw => (dirField_dbar h hw).trans (hρ w hw).symm) proj
  have eqcl : EqOn W (canonicalField ρ) (closure upper) := eq.of_subset_closure
    (by rw [closure_upper_plane]; exact (dirField_smooth h).continuousOn)
    (canonicalField_continuous src.green.quadratic).continuousOn subset_closure (Subset.rfl)
  have hz' : z∈closure upper := by rwa [closure_upper_plane]
  rw [show dirField V z=canonicalField ρ z from eqcl hz',canonicalField_eq_integral src.green.quadratic,←integral_neg,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
  rw [hρ w hw]; ring

end Liu
