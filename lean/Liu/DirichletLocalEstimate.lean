module

public import Liu.DirichletParametrix

@[expose] public section

noncomputable section
open Set Filter Metric MeasureTheory Real Complex InnerProductSpace
open scoped Topology ContDiff ComplexConjugate
namespace Liu

private theorem regular_pair_bound {V : ℂ → ℂ} {R M A : ℝ} (hR : 0<R) (hM : 0≤M) (hA : 0≤A)
    {z : ℂ} (hz : z∈closedUpper)
    (hK : ∀ w, ‖Laplacian.laplacian (regularResolvent R z) w‖≤M/R^3)
    (hout : ∀ w∈upper, R≤‖z-w‖ → Laplacian.laplacian (regularResolvent R z) w=0)
    (hV : ∀ w∈upper, ‖z-w‖<R → ‖V w‖≤A) :
    ‖∫ w, V w*dirLap (regularResolvent R z) w ∂upperArea‖≤M*A/R := by
  obtain ⟨hi,hball⟩ := upper_ball_indicator_bound z hR
  let c := A*(M/R^3)
  have c₀ : 0≤c := by dsimp [c]; positivity
  apply (norm_integral_le_of_norm_le (hi.const_mul c) ?_).trans
  · rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hball c₀).trans_eq (by dsimp [c]; field_simp <;> ring)
  · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
    rw [norm_mul,dirLap_inside (regularResolvent_smooth R z).contDiffOn hw]
    by_cases hp : ‖z-w‖<R
    · have hh : w∈ball z R := by simpa only [mem_ball,dist_eq_norm,norm_sub_rev w z] using hp
      rw [indicator_of_mem hh,mul_one]
      exact mul_le_mul (hV w hw hp) (hK w) (norm_nonneg _) hA
    · have hh : w∉ball z R := by simpa only [mem_ball,dist_eq_norm,norm_sub_rev w z] using hp
      rw [indicator_of_notMem hh,hout w hw (le_of_not_gt hp),norm_zero,mul_zero,mul_zero]

theorem dirField_ball_estimate :
    ∃ C≥0, ∀ {V : ℂ → ℂ}, ContDiffOn ℝ ∞ V closedUpper → (∀ x : ℝ, V x=0) →
    ∀ {z : ℂ}, z∈closedUpper → ∀ {R A B : ℝ}, 0<R → 0≤A → 0≤B →
    (∀ w∈upper, ‖z-w‖<R → ‖V w‖≤A) →
    (∀ w∈upper, ‖z-w‖<R → ‖dirLap V w‖≤B) →
    ‖dirField V z‖≤C*(A/R+R*B) := by
  obtain ⟨M,hM,H⟩ := regularResolvent_bounds
  let q := (1/π)*(∫ w, localInverse 0 w)
  have hq : 0≤q := mul_nonneg (by positivity) (integral_nonneg fun w => indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) w)
  let C := M+2*(2+M)*q
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro V hV hb z hz R A B hR hA hB ha hl
  obtain ⟨hreg,hK,hout⟩ := H R hR z
  obtain ⟨hJ,hP,he⟩ := localized_dirichlet_formula hV hb hR hz
  have hP' := regular_pair_bound hR hM hA hz hK (fun w hw hr => (hout w hz hw hr).2) ha
  let J := fun w => (greenResolvent z w-regularResolvent R z w)*dirLap V w
  have ha₁ := local_resolvent_remainder hM hR z hz hreg (fun w hw hr => (hout w hz hw hr).1)
  have hr' : 0<2*R := by positivity
  obtain ⟨hi,hweight⟩ := scaledWeight_estimate hr' z
  let k := (2+M)/(2*R)*B
  have hk : 0≤k := by dsimp [k]; positivity
  have hJ' : ‖∫ w, J w ∂upperArea‖ ≤ 2*(2+M)*q*(R*B) := by
    apply (norm_integral_le_of_norm_le (hi.const_mul k) ?_).trans
    · rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left hweight hk).trans_eq (by dsimp [k,q]; field_simp <;> ring)
    · filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet,ha₁] with w hw hw'
      have hnn : 0 ≤ scaledWeight (2*R) z w := indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) _
      change ‖(greenResolvent z w-regularResolvent R z w)*dirLap V w‖≤k*scaledWeight (2*R) z w
      rw [norm_mul]
      by_cases near : ‖z-w‖<R
      · exact (mul_le_mul hw' (hl w hw near) (norm_nonneg _) (by positivity)).trans_eq (by dsimp [k]; ring)
      · rw [(hout w hz hw (le_of_not_gt near)).1,sub_self,norm_zero,zero_mul]
        positivity
  rw [he,norm_mul]
  have ht : ‖(1/2:ℂ)‖≤1 := by norm_num
  apply (mul_le_of_le_one_left (norm_nonneg _) ht).trans ((norm_add_le ..).trans _)
  apply (add_le_add hJ' hP').trans
  have h₁ : M≤C := le_add_of_nonneg_right (by positivity)
  have h₂ : 2*(2+M)*q≤C := le_add_of_nonneg_left hM
  calc
    _ = 2*(2+M)*q*(R*B)+M*(A/R) := by ring
    _ ≤ C*(R*B)+C*(A/R) := add_le_add (mul_le_mul_of_nonneg_right h₂ (by positivity)) (mul_le_mul_of_nonneg_right h₁ (by positivity))
    _ = _ := by ring

/-- Send the localization radius to infinity. The two regular-kernel errors
vanish for bounded V with integrable Laplacian, yielding its gradient
representation for the genuine reflected Green kernel. -/
theorem bounded_dirField_representation {V : ℂ → ℂ} (hV : ContDiffOn ℝ ∞ V closedUpper)
    (hb : ∀ x : ℝ, V x=0) {A : ℝ} (hA : 0≤A) (ha : ∀ w∈upper, ‖V w‖≤A)
    (hL : Integrable (dirLap V) upperArea) {z : ℂ} (hz : z∈closedUpper)
    (hJ : Integrable (fun w => greenResolvent z w*dirLap V w) upperArea) :
    dirField V z=(1/2:ℂ)*(∫ w, greenResolvent z w*dirLap V w ∂upperArea) := by
  obtain ⟨M,hM,H⟩ := regularResolvent_bounds
  let D := ‖dirField V z-(1/2:ℂ)*(∫ w, greenResolvent z w*dirLap V w ∂upperArea)‖
  have bound (R : ℝ) (hR : 0<R) : D≤(M*A+M*(∫ w, ‖dirLap V w‖ ∂upperArea))/R := by
    obtain ⟨hreg,hK,hout⟩ := H R hR z
    have Eq := (localized_dirichlet_formula hV hb hR hz).2.2
    have hP := regular_pair_bound hR hM hA hz hK (fun w hw hr => (hout w hz hw hr).2) (fun w hw _ => ha w hw)
    let K := regularResolvent R z
    have hi : Integrable (fun w => K w*dirLap V w) upperArea := hL.bdd_mul (regularResolvent_smooth R z).continuous.aestronglyMeasurable (ae_of_all _ hreg)
    have hk : ‖∫ w, K w*dirLap V w ∂upperArea‖ ≤ (M/R)*∫ w, ‖dirLap V w‖ ∂upperArea := by
      rw [←integral_const_mul]
      apply norm_integral_le_of_norm_le (hL.norm.const_mul (M/R))
      exact ae_of_all _ (fun w => (norm_mul ..).le.trans (mul_le_mul_of_nonneg_right (hreg w) (norm_nonneg _)))
    simp only [sub_mul] at Eq
    rw [integral_sub hJ hi] at Eq
    dsimp only [D]
    rw [Eq,←mul_sub,norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (by norm_num : ‖(1/2:ℂ)‖≤1)).trans
    rw [show ∀ a b c : ℂ, a-b+c-a=c-b by intros; ring]
    exact (norm_sub_le ..).trans ((add_le_add hP hk).trans_eq (by ring))
  have lim : Tendsto (fun R : ℝ => (M*A+M*(∫ w, ‖dirLap V w‖ ∂upperArea))/R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (ge_of_tendsto lim ((eventually_gt_atTop (0:ℝ)).mono fun _ h => bound _ h)) (norm_nonneg _)))

end Liu
