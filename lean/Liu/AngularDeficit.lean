import Liu.Witness
import Liu.RadialEnergy

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

def angularDeficit (θ : ℝ) := k₀ - (π/2-θ)^2

theorem angularDeficit_mean : (∫ θ in Ioo (0:ℝ) π, angularDeficit θ) = 0 := by
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le pi_pos.le]
  let f := fun θ : ℝ => k₀*θ + (π/2-θ)^3/3
  have h (u : ℝ) : HasDerivAt f (angularDeficit u) u := by
    have d := (hasDerivAt_id u)
    convert (d.const_mul k₀).add (((d.const_sub (π/2)).pow 3).div_const 3) using 1
    · rfl
    · dsimp [angularDeficit,id]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => h x) (by
    apply Continuous.intervalIntegrable; unfold angularDeficit; fun_prop)]
  dsimp [f,k₀]; ring

/-- Separation of radial and angular factors in the normalized upper-half-plane integral. -/
theorem upperArea_separated (f g : ℝ → ℝ) :
    (∫ z : ℂ, f ‖z‖ * g z.arg ∂upperArea) =
    (∫ z : ℂ, f ‖z‖ ∂upperArea)*((1/π)*∫ x in Ioo (0:ℝ) π, g x) := by
  classical
  let θ := Ioo (0:ℝ) π
  let θall := Ioo (-π) π
  have sub : θ ⊆ θall := Ioo_subset_Ioo (by linarith [pi_pos]) le_rfl
  have angle : (∫ t in θall, θ.indicator g t) = ∫ t in θ, g t := by
    rw [setIntegral_indicator measurableSet_Ioo,inter_eq_right.mpr sub]
  rw [upperArea_radial]
  unfold upperArea area
  rw [Measure.restrict_smul,integral_smul_measure,←integral_indicator upper_open.measurableSet,
    ←Complex.integral_comp_polarCoord_symm,polarCoord_target]
  rw [smul_eq_mul]
  suffices h : (∫ v in Ioi (0:ℝ) ×ˢ θall,
      v.1 • upper.indicator (fun z : ℂ => f ‖z‖ * g z.arg) (Complex.polarCoord.symm v)) =
      (∫ r in Ioi (0:ℝ), r*f r)*(∫ u in θ, g u) by rw [h,ENNReal.toReal_ofReal (by positivity : 0≤1/π)]; dsimp only [θ]; ring
  calc
    _ = (∫ r in Ioi (0:ℝ), r*f r) * ∫ t in θall, θ.indicator g t := by
      rw [←setIntegral_prod_mul,Measure.volume_eq_prod]
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro v hv
      have hp : v ∈ Complex.polarCoord.target := hv
      have he := Complex.polarCoord.right_inv hp
      rw [Complex.polarCoord_apply] at he
      have hr := congrArg Prod.fst he
      have ht := congrArg Prod.snd he
      change ‖Complex.polarCoord.symm v‖ = v.1 at hr
      change (Complex.polarCoord.symm v).arg = v.2 at ht
      have him : (Complex.polarCoord.symm v).im = v.1 * sin v.2 := by
        simp [←Complex.ofReal_sin,←Complex.ofReal_cos]
      have hu : Complex.polarCoord.symm v ∈ upper ↔ 0 < v.2 := by
        change 0 < (Complex.polarCoord.symm v).im ↔ _
        rw [him]
        constructor
        · intro h
          by_contra! hh
          exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hv.1)
            (sin_nonpos_of_nonpos_of_neg_pi_le hh hv.2.1.le))) h
        · intro hy
          exact mul_pos hv.1 (sin_pos_of_pos_of_lt_pi hy hv.2.2)
      by_cases hy : 0 < v.2
      · simp only [indicator_of_mem (hu.mpr hy),indicator_of_mem (show v.2 ∈ θ from ⟨hy,hv.2.2⟩),hr,ht,smul_eq_mul]
        ring
      · simp only [indicator_of_notMem (mt hu.mp hy),indicator_of_notMem (show v.2 ∉ θ from fun h => hy h.1),smul_zero,mul_zero]
    _ = _ := by rw [angle]

/-- Angular mean zero makes the signed leading term vanish on every radial cutoff. -/
theorem upperArea_angular_cancel (f : ℝ → ℝ) :
    (∫ z : ℂ, f ‖z‖ * angularDeficit z.arg ∂upperArea) = 0 := by
  rw [upperArea_separated,angularDeficit_mean,mul_zero,mul_zero]

def leadingDeficit (m : ℝ) (z : ℂ) := m^2*radialTail 2 z*angularDeficit z.arg

theorem halfDisc_leadingDeficit (m R : ℝ) :
    ∫ z in halfDisc R, leadingDeficit m z ∂area = 0 := by
  classical
  have h := upperArea_angular_cancel (fun r => if r<R then m^2*(if 1<r then r^(-(2:ℝ)) else 0) else 0)
  have hs : MeasurableSet (Metric.ball (0:ℂ) R) := Metric.isOpen_ball.measurableSet
  have heq : (∫ z in halfDisc R, leadingDeficit m z ∂area) =
      ∫ z, (Metric.ball (0:ℂ) R).indicator (leadingDeficit m) z ∂upperArea := by
    rw [integral_indicator hs,upperArea,Measure.restrict_restrict hs,inter_comm]; rfl
  rw [heq,←h]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hr : ‖z‖ < R
  · have hB : z ∈ Metric.ball (0:ℂ) R := by simpa using hr
    simp [indicator_of_mem hB,leadingDeficit,radialTail,hr]
  · have hB : z ∉ Metric.ball (0:ℂ) R := by simpa using hr
    simp [hB,hr]

end Liu
