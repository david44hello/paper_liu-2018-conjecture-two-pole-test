module

public import Liu.RadialEnergy

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter Metric
open scoped Topology
namespace Liu

/-- For a radial nonnegative majorant around a lower pole, translating the
upper half-plane away from the origin only decreases its integral. -/
theorem translated_radial_majorant {F : ℝ → ℝ} {K : ℝ} (hK : 0<K)
    (hF : ∀ r≥0, 0≤F r) (hm : (∫ r in Ioi (0:ℝ), r*F r)=K)
    {w : ℂ} (hw : w.im≤0) :
    Integrable (fun z : ℂ => F ‖z-w‖) upperArea ∧ (∫ z : ℂ, F ‖z-w‖ ∂upperArea)≤K := by
  let f := fun z : ℂ => F ‖z‖
  have hI : (∫ z, f z ∂upperArea) = K := (upperArea_radial F).trans hm
  have hi : IntegrableOn f upper area := by
    change Integrable f upperArea
    contrapose! hK
    rw [integral_undef hK] at hI
    exact hI.ge
  let D := {z : ℂ | -w.im<z.im}
  have hD : D ⊆ upper := fun z hz => (neg_nonneg.mpr hw).trans_lt hz
  have hp : MeasurePreserving (fun z : ℂ => z+ -w) area area := by
    have h := measurePreserving_add_right (volume:Measure ℂ) (-w)
    exact ⟨h.measurable,by unfold area; rw [Measure.map_smul _ h.measurable.aemeasurable,h.map_eq]⟩
  have he := (Homeomorph.addRight (-w)).measurableEmbedding
  have hpre : (fun z : ℂ => z+ -w) ⁻¹' D=upper := by
    ext z; change -w.im<(z+ -w).im ↔ 0<z.im
    simp
  have hi' := (hp.integrableOn_comp_preimage he).mpr (hi.mono_set hD)
  have he' := hp.setIntegral_preimage_emb he f D
  rw [hpre] at hi' he'
  have hle := setIntegral_mono_set hi (ae_of_all _ fun z => hF _ (norm_nonneg z)) (ae_of_all area fun _ hz => hD hz)
  exact ⟨by simpa only [upperArea,IntegrableOn,f,Function.comp_def,sub_eq_add_neg] using hi',
    he'.trans_le (hle.trans_eq hI)⟩

def radialDisc (R r : ℝ) := if r≤R then 1 else (0:ℝ)
def radialInvDisc (R r : ℝ) := if r≤R then r⁻¹ else 0
def radialInvAnnulus (a b r : ℝ) := (Ioc a b).indicator (fun t => (t^2)⁻¹) r
def radialInvTail (k : ℕ) (b r : ℝ) := (Ioi b).indicator (fun t => (t^k)⁻¹) r

theorem radialDisc_majorant {w : ℂ} (hw : w.im≤0) {R : ℝ} (hR : 0<R) :
    Integrable (fun z : ℂ => radialDisc R ‖z-w‖) upperArea ∧
    (∫ z : ℂ, radialDisc R ‖z-w‖ ∂upperArea)≤R^2/2 := by
  apply translated_radial_majorant (by positivity) _ _ hw
  · intro r hr; unfold radialDisc; split <;> norm_num
  · have he (r : ℝ) (hr : r∈Ioi (0:ℝ)) : r*radialDisc R r=(Ioc 0 R).indicator (fun x => x) r := by
      by_cases h : r≤R <;> simp [radialDisc,h,indicator,show 0<r from hr,mem_Ioc]
    rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr Ioc_subset_Ioi_self,←intervalIntegral.integral_of_le hR.le,integral_id]
    ring

theorem radialInvDisc_majorant {w : ℂ} (hw : w.im≤0) {R : ℝ} (hR : 0<R) :
    Integrable (fun z : ℂ => radialInvDisc R ‖z-w‖) upperArea ∧
    (∫ z : ℂ, radialInvDisc R ‖z-w‖ ∂upperArea)≤R := by
  apply translated_radial_majorant hR _ _ hw
  · intro r hr; unfold radialInvDisc; split <;> positivity
  · have he (r : ℝ) (hr : r∈Ioi (0:ℝ)) : r*radialInvDisc R r=(Ioc 0 R).indicator (fun _ => (1:ℝ)) r := by
      by_cases h : r≤R <;> simp [radialInvDisc,h,indicator,show 0<r from hr,mem_Ioc,(show 0<r from hr).ne']
    rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr Ioc_subset_Ioi_self,←intervalIntegral.integral_of_le hR.le]
    simp

theorem radialInvAnnulus_majorant {w : ℂ} (hw : w.im≤0) {a b : ℝ} (ha : 0<a) (hab : a<b) :
    Integrable (fun z : ℂ => radialInvAnnulus a b ‖z-w‖) upperArea ∧
    (∫ z : ℂ, radialInvAnnulus a b ‖z-w‖ ∂upperArea)≤log (b/a) := by
  apply translated_radial_majorant (log_pos ((one_lt_div ha).mpr hab)) _ _ hw
  · intro r _; apply indicator_nonneg; intro x _; positivity
  · have he (r : ℝ) (hr : r∈Ioi (0:ℝ)) :
        r*radialInvAnnulus a b r=(Ioc a b).indicator (fun t => t⁻¹) r := by
      by_cases h : r∈Ioc a b
      · simp [radialInvAnnulus,h]; field_simp [(show 0<r from hr).ne']
      · simp [radialInvAnnulus,h]
    rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Ioc,
      inter_eq_right.mpr (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha.le)),←intervalIntegral.integral_of_le hab.le,
      integral_inv_of_pos ha (ha.trans hab)]

theorem radialInvTail_majorant {w : ℂ} (hw : w.im≤0) {b : ℝ} (hb : 0<b)
    {k : ℕ} (hk : 2<k) :
    Integrable (fun z : ℂ => radialInvTail k b ‖z-w‖) upperArea ∧
    (∫ z : ℂ, radialInvTail k b ‖z-w‖ ∂upperArea)≤b^(2-(k:ℝ))/((k:ℝ)-2) := by
  have hk' : (2:ℝ)<k := by exact_mod_cast hk
  apply translated_radial_majorant (div_pos (rpow_pos_of_pos hb _) (sub_pos.mpr hk')) _ _ hw
  · intro r hr; by_cases h : r∈Ioi b <;> simp [radialInvTail,h]; positivity
  · have he (r : ℝ) (hr : r∈Ioi (0:ℝ)) :
        r*radialInvTail k b r=(Ioi b).indicator (fun t => t^(1-(k:ℝ))) r := by
      by_cases h : r∈Ioi b
      · simp [radialInvTail,h,Real.rpow_sub (show 0<r from hr),div_eq_mul_inv]
      · simp [radialInvTail,h]
    rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi hb.le),integral_Ioi_rpow_of_lt (by linarith) hb,
      show 1-(k:ℝ)+1=2-k by ring,show (2:ℝ)-k= -((k:ℝ)-2) by ring,neg_div_neg_eq]
end Liu
