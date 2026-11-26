import Liu.DirichletDerivatives
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

noncomputable section
open Set Filter MeasureTheory Real Complex Metric InnerProductSpace
open scoped Topology ContDiff ComplexConjugate
namespace Liu

private def coreBump : ContDiffBump (0:ℂ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
def smoothInverse (w : ℂ) : ℂ := (1-(coreBump w:ℂ))/w

theorem smoothInverse_regular : ContDiff ℝ ∞ smoothInverse := by
  apply contDiff_iff_contDiffAt.mpr
  intro w
  by_cases hw : w=0
  · subst w
    apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [coreBump.eventuallyEq_one] with x hx
    simp [smoothInverse,show coreBump x=1 from hx]
  · have H : ContDiffAt ℝ ∞ (fun x : ℂ => (coreBump x:ℂ)) w := (Complex.ofRealCLM.contDiff.comp coreBump.contDiff).contDiffAt
    have hi : ContDiffAt ℝ ∞ (fun z : ℂ => z⁻¹) w := (analyticAt_id.inv hw : AnalyticAt ℂ (fun x : ℂ => x⁻¹) w).contDiffAt.restrict_scalars ℝ
    unfold smoothInverse
    simp only [div_eq_mul_inv]
    exact ((contDiffAt_const (c:=(1:ℂ))).sub H).mul hi

theorem smoothInverse_outer {w : ℂ} (h : 1/2≤‖w‖) : smoothInverse w=w⁻¹ := by
  simp [smoothInverse,coreBump.zero_of_le_dist (by simpa [coreBump] using h)]

theorem smoothInverse_bounds :
    ∃ M≥0, ∀ w : ℂ, ‖smoothInverse w‖≤M ∧ ‖Laplacian.laplacian smoothInverse w‖≤M ∧
    (1/2<‖w‖ → Laplacian.laplacian smoothInverse w=0) := by
  have hc : Continuous (Laplacian.laplacian smoothInverse) := by
    rw [laplacian_eq_iteratedFDeriv_complexPlane]
    have h := smoothInverse_regular.continuous_iteratedFDeriv (m:=2) (by simp)
    exact (continuous_eval.comp (h.prodMk continuous_const)).add (continuous_eval.comp (h.prodMk continuous_const))
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn smoothInverse_regular.continuous.continuousOn
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn hc.continuousOn
  have outer (w : ℂ) (hw : 1/2<‖w‖) : Laplacian.laplacian smoothInverse w=0 := by
    have eq : smoothInverse=ᶠ[𝓝 w] (fun x => x⁻¹) := by
      filter_upwards [continuous_norm.continuousAt.eventually (Ioi_mem_nhds hw)] with x hx using smoothInverse_outer hx.le
    have hn : w≠0 := norm_pos_iff.mp (by linarith)
    exact (laplacian_congr_nhds eq).eq_of_nhds.trans ((analyticAt_id.inv hn).harmonicAt.2.eq_of_nhds)
  refine ⟨max 1 (max A B),le_trans zero_le_one (le_max_left ..),fun w => ⟨?_,?_,outer w⟩⟩
  · by_cases h : ‖w‖≤1
    · exact (hA w (by simpa using h)).trans ((le_max_left A B).trans (le_max_right ..))
    · rw [smoothInverse_outer (by linarith),norm_inv]
      exact (inv_le_one_of_one_le₀ (le_of_not_ge h)).trans (le_max_left ..)
  · by_cases h : ‖w‖≤1
    · exact (hB w (by simpa using h)).trans ((le_max_right A B).trans (le_max_right ..))
    · rw [outer w (by linarith),norm_zero]; exact zero_le_one.trans (le_max_left ..)

private theorem lap_affine {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (A : ℂ →L[ℝ] ℂ)
    (b x : ℂ) {s t : ℝ} (h₁ : A 1=s • (1:ℂ)) (h₂ : A I=t • I) (he : s^2=t^2) :
    Laplacian.laplacian (fun w => f (b+A w)) x = s^2 • Laplacian.laplacian f (b+A x) := by
  let g := fun y => f (b+y)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  change Laplacian.laplacian (g ∘ A) x=_
  rw [laplacian_eq_iteratedFDeriv_complexPlane,laplacian_eq_iteratedFDeriv_complexPlane f]
  dsimp only
  rw [A.iteratedFDeriv_comp_right hg _ (by simp : (2:ℕ)≤(∞:ℕ∞ω))]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,g,iteratedFDeriv_comp_add_left]
  let D := iteratedFDeriv ℝ 2 f (b+A x)
  have H (v : ℂ) (u : ℝ) (hu : A v=u • v) : D (fun i => A (![v,v] i)) = u^2 • D ![v,v] := by
    have e : (fun i : Fin 2 => A (![v,v] i)) = fun i => u • (![v,v] i) := by funext i; fin_cases i <;> simpa using hu
    rw [e,D.map_smul_univ (fun _ => u)]
    simp
  rw [H 1 s h₁,H I t h₂,←he,smul_add]

def scaledSmoothInverse (R : ℝ) (w : ℂ) : ℂ := R⁻¹ • smoothInverse (R⁻¹ • w)

def regularResolvent (R : ℝ) (z w : ℂ) := scaledSmoothInverse R (z-conj w)-scaledSmoothInverse R (z-w)

theorem regularResolvent_smooth (R : ℝ) (z : ℂ) : ContDiff ℝ ∞ (regularResolvent R z) := by
  unfold regularResolvent scaledSmoothInverse
  have hc : ContDiff ℝ ∞ (conj : ℂ → ℂ) := Complex.conjCLE.toContinuousLinearMap.contDiff
  exact ((smoothInverse_regular.comp ((contDiff_const.sub hc).const_smul _)).const_smul _).sub
    ((smoothInverse_regular.comp ((contDiff_const.sub contDiff_id).const_smul _)).const_smul _)

theorem regularResolvent_bottom (R : ℝ) (z : ℂ) (x : ℝ) : regularResolvent R z x=0 := by
  simp [regularResolvent]

private theorem lap_scaled_inverse (R : ℝ) (z w : ℂ) (A : ℂ →L[ℝ] ℂ)
    (h₁ : A 1=1) (h₂ : A I=I ∨ A I= -I) :
    Laplacian.laplacian (fun x => scaledSmoothInverse R (z-A x)) w =
      R⁻¹^3 • Laplacian.laplacian smoothInverse (R⁻¹ • (z-A w)) := by
  let T := (-R⁻¹) • A
  have e (x : ℂ) : R⁻¹ • (z-A x)=R⁻¹ • z+T x := by simp [T,smul_sub,sub_eq_add_neg]
  have hd : ContDiff ℝ ∞ (fun x => smoothInverse (R⁻¹ • z+T x)) :=
    smoothInverse_regular.comp (contDiff_const.add (show ContDiff ℝ ∞ T from T.contDiff))
  simp only [scaledSmoothInverse,e]
  erw [laplacian_smul R⁻¹ (hd.contDiffAt.of_le (by simp))]
  have t₁ : T 1=(-R⁻¹) • (1:ℂ) := by simp [T,h₁]
  rcases h₂ with h₂ | h₂
  · rw [lap_affine smoothInverse_regular T _ _ t₁ (show T I=(-R⁻¹) • I by simp [T,h₂]) rfl,smul_smul]
    congr 1; ring
  · rw [lap_affine smoothInverse_regular T _ _ t₁ (show T I=R⁻¹ • I by simp [T,h₂]) (by ring),smul_smul]
    congr 1; ring

theorem regularResolvent_lap (R : ℝ) (z w : ℂ) :
    Laplacian.laplacian (regularResolvent R z) w =
      R⁻¹^3 • (Laplacian.laplacian smoothInverse (R⁻¹ • (z-conj w))-
          Laplacian.laplacian smoothInverse (R⁻¹ • (z-w))) := by
  have hs (A : ℂ →L[ℝ] ℂ) : ContDiff ℝ ∞ (fun x => scaledSmoothInverse R (z-A x)) := by
    unfold scaledSmoothInverse
    exact (smoothInverse_regular.comp ((contDiff_const.sub A.contDiff).const_smul _)).const_smul _
  let idc := ContinuousLinearMap.id ℝ ℂ
  change Laplacian.laplacian ((fun x => scaledSmoothInverse R (z-Complex.conjCLE.toContinuousLinearMap x))-
    (fun x => scaledSmoothInverse R (z-idc x))) w=_
  rw [ContDiffAt.laplacian_sub ((hs _).contDiffAt.of_le (by simp)) ((hs _).contDiffAt.of_le (by simp)),
    lap_scaled_inverse R z w _ (by simp) (Or.inr (by simp)),
    lap_scaled_inverse R z w idc rfl (Or.inl rfl)]
  simp only [smul_sub,idc,ContinuousLinearMap.id_apply,ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply]

end Liu
