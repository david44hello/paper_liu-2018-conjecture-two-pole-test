import Liu.CapMoments
import Liu.IntegrableReproducing

noncomputable section
open Set MeasureTheory Real Filter Finset
open scoped Topology ComplexConjugate InnerProductSpace
namespace Liu

def upperMonomial (n : ℕ) (z : ℂ) :=
  (-2*Complex.I)*bergmanKernel Complex.I z*(cayleyInv Complex.I z)^n

theorem cayleyPull_upperMonomial (n : ℕ) {w : ℂ} (hw : w∈disc) :
    cayleyPull Complex.I (upperMonomial n) w=w^n := by
  have hz : Complex.I∈upper := by simp [upper]
  have h := cayleyPull_kernel hz hw
  rw [Complex.conj_I,sub_neg_eq_add,←two_mul] at h
  dsimp only [cayleyPull,upperMonomial]
  rw [(cayley_inv_left hz hw).2]
  change (-2*Complex.I)*bergmanKernel Complex.I (cayley Complex.I w)*w^n*cayleyJac Complex.I w=_
  rw [show (-2*Complex.I)*bergmanKernel Complex.I (cayley Complex.I w)*w^n*cayleyJac Complex.I w =
    (-2*Complex.I)*cayleyPull Complex.I (bergmanKernel Complex.I) w*w^n by unfold cayleyPull; ring,h]
  field_simp [Complex.I_ne_zero]

private theorem upperMonomial_measurable (n : ℕ) : Measurable (upperMonomial n) := by unfold upperMonomial bergmanKernel cayleyInv; fun_prop

theorem upperMonomial_memLp (n : ℕ) : MemLp (upperMonomial n) 2 upperArea := by
  apply (memLp_two_iff_integrable_sq_norm (upperMonomial_measurable n).aestronglyMeasurable).mpr
  apply (cayleyPull_normSq_integrable_iff (show Complex.I∈upper by simp [upper]) _).mpr
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  apply ((show Continuous (fun w : ℂ => ‖w^n‖^2) by fun_prop).continuousOn.integrableOn_compact (μ:=area)
    (isCompact_closedBall (0:ℂ) 1) |>.mono_set Metric.ball_subset_closedBall).congr_fun _ Metric.isOpen_ball.measurableSet
  intro w hw; dsimp only; rw [cayleyPull_upperMonomial n hw]

theorem upperMonomial_analytic (n : ℕ) : DifferentiableOn ℂ (upperMonomial n) upper := by
  intro w hw
  have hn : w-conj Complex.I≠0 := fun he => by
    have hh := congrArg Complex.im (sub_eq_zero.mp he); simp at hh; linarith [show 0<w.im from hw]
  unfold upperMonomial bergmanKernel cayleyInv
  fun_prop (disch := first | assumption | exact pow_ne_zero 2 hn)

def upperUnitMonomial (n : ℕ) : PlaneL2 :=
  ((√((n:ℝ)+1):ℝ):ℂ) • (upperMonomial_memLp n).toLp (upperMonomial n)

theorem cayley_pairing (f g : ℂ → ℂ) :
    (∫ z, g z*conj (f z) ∂upperArea)=
      ∫ w in disc, cayleyPull Complex.I g w*conj (cayleyPull Complex.I f w) ∂area := by
  rw [upperArea,cayley_area_integral (show Complex.I∈upper by simp [upper])]
  apply integral_congr_ae; filter_upwards with w
  simp only [cayleyPull,Complex.real_smul,Complex.ofReal_pow,←Complex.mul_conj',map_mul]; ring

theorem upperMonomial_inner {h : ℂ → ℂ} (hh : MemLp h 2 upperArea) (n : ℕ) :
    inner ℂ ((upperMonomial_memLp n).toLp (upperMonomial n)) (hh.toLp h)=
      ∫ w in disc, cayleyPull Complex.I h w*conj (w^n) ∂area := by
  rw [L2.inner_def,←setIntegral_congr_fun (s:=disc) Metric.isOpen_ball.measurableSet
    (f:=fun w => cayleyPull Complex.I h w*conj (cayleyPull Complex.I (upperMonomial n) w))
    (g:=fun w => cayleyPull Complex.I h w*conj (w^n)) (fun w hw => by dsimp only; rw [cayleyPull_upperMonomial n hw]),←cayley_pairing]
  apply integral_congr_ae
  filter_upwards [hh.coeFn_toLp,(upperMonomial_memLp n).coeFn_toLp] with z hz hk
  rw [hz,hk,RCLike.inner_apply]

theorem upperUnitMonomial_orthonormal : Orthonormal ℂ upperUnitMonomial := by
  rw [orthonormal_iff_ite]; intro n m
  rw [upperUnitMonomial,upperUnitMonomial,inner_smul_left,inner_smul_right,upperMonomial_inner]
  rw [setIntegral_congr_fun (s:=disc) Metric.isOpen_ball.measurableSet
    (g:=fun w => w^m*conj (w^n)) (fun w hw => by rw [cayleyPull_upperMonomial m hw]),disc_monomial_pairing]
  by_cases he : n=m
  · subst m
    simp only [if_pos rfl,Complex.conj_ofReal]
    rw [←mul_assoc,←Complex.ofReal_mul,Real.mul_self_sqrt (by positivity : 0≤(n:ℝ)+1)]
    push_cast; field_simp
  · simp [he,Ne.symm he]

theorem upperUnitMonomial_analytic_mem (n : ℕ) : upperUnitMonomial n∈analyticSubspace := by
  letI : analyticSubspace.HasOrthogonalProjection := by unfold analyticSubspace; infer_instance
  apply analyticSubspace.smul_mem
  exact Submodule.starProjection_eq_self_iff.mp (project_fixes_analytic (upperMonomial_memLp n) (upperMonomial_analytic n))

end Liu
