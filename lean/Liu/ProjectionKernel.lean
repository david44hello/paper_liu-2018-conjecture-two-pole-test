import Liu.Reproducing

noncomputable section
open Set MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace Liu

def bergmanIntegral (h : ℂ → ℂ) (z : ℂ) := ∫ w, h w*conj (bergmanKernel z w) ∂upperArea

private theorem inner_toLp {f h : ℂ → ℂ} (hf : MemLp f 2 upperArea) (hh : MemLp h 2 upperArea) :
    inner ℂ (hf.toLp f) (hh.toLp h) = ∫ w, h w*conj (f w) ∂upperArea := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hh.coeFn_toLp] with w hu hv
  rw [hu,hv,RCLike.inner_apply]

/-- Integral representative of the actual Hilbert-space Bergman projection. -/
theorem projection_has_kernel {h : ℂ → ℂ} (hh : MemLp h 2 upperArea) :
    ∃ g : ℂ → ℂ, ∃ hg : MemLp g 2 upperArea, DifferentiableOn ℂ g upper ∧
      project (hh.toLp h) = hg.toLp g ∧ EqOn g (bergmanIntegral h) upper := by
  letI : analyticSubspace.HasOrthogonalProjection := by unfold analyticSubspace; infer_instance
  have hm : project (hh.toLp h) ∈ analyticSubspace := analyticSubspace.starProjection_apply_mem _
  rw [bergman_projection_range] at hm
  obtain ⟨g,hg,hd,hgRep⟩ := hm
  refine ⟨g,hg,hd,hgRep,?_⟩
  intro z hz
  have hK := bergmanKernel_memLp hz
  have hkHol := bergmanKernel_analytic hz
  have hproj := project_fixes_analytic hK hkHol
  have hsym := analyticSubspace.inner_starProjection_left_eq_right (hK.toLp _) (hh.toLp h)
  change inner ℂ (project (hK.toLp _)) (hh.toLp h) = inner ℂ (hK.toLp _) (project (hh.toLp h)) at hsym
  rw [hproj,hgRep,inner_toLp hK hh,inner_toLp hK hg,bergman_reproducing hg hd hz] at hsym
  exact hsym.symm

theorem critical_residual_integral {f : ℂ → ℂ} (hf : MemLp f 2 upperArea)
    (hd : DifferentiableOn ℂ f upper) (hh : MemLp (logInput f) 2 upperArea) :
    ∃ G : ℂ → ℂ, ∃ hG : MemLp G 2 upperArea,
      hG.toLp G = asL2 (logInput f)-project (asL2 (logInput f)) ∧
      ∀ z ∈ upper, G z = ∫ w, (f w * ((Real.log ‖f z‖-Real.log ‖f w‖:ℝ):ℂ))*
        conj (bergmanKernel z w) ∂upperArea := by
  obtain ⟨g,hg,_,hrep,heval⟩ := projection_has_kernel hh
  let G := logInput f-g
  have hG : MemLp G 2 upperArea := hh.sub hg
  refine ⟨G,hG,?_,?_⟩
  · simp only [asL2,dif_pos hh,hrep,G,MemLp.toLp_sub hh hg]
  intro z hz
  have hK := bergmanKernel_memLp hz
  have hkconj : MemLp (fun w => conj (bergmanKernel z w)) 2 upperArea := by
    apply hK.congr_norm
    · exact Complex.continuous_conj.comp_aestronglyMeasurable hK.aestronglyMeasurable
    · exact ae_of_all _ fun _ => (Complex.norm_conj _).symm
  have hfK : Integrable (fun w => f w*conj (bergmanKernel z w)) upperArea := hf.integrable_mul hkconj
  have hhK : Integrable (fun w => logInput f w*conj (bergmanKernel z w)) upperArea := hh.integrable_mul hkconj
  let c : ℂ := (Real.log ‖f z‖:ℂ)
  have hdiff (w : ℂ) : (f w*((Real.log ‖f z‖-Real.log ‖f w‖:ℝ):ℂ))*conj (bergmanKernel z w) =
      c*(f w*conj (bergmanKernel z w))-(logInput f w)*conj (bergmanKernel z w) := by
    dsimp [logInput,c]; push_cast; ring
  simp_rw [hdiff]
  rw [integral_sub (hfK.const_mul c) hhK,integral_const_mul,bergman_reproducing hf hd hz]
  change logInput f z - g z = _
  rw [heval hz]
  simp only [bergmanIntegral,logInput,c]; ring

end Liu
