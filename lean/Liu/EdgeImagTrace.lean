import Liu.EdgeImagMajorant
import Liu.EdgeRealTrace

noncomputable section
open Set Real MeasureTheory
namespace Liu

/-- The normalized L² estimate for the imaginary Poisson trace in E.3(a). -/
theorem edge_imag_trace_separated {s γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hc : 1/2≤cos γ)
    (hu : 0≤u) :
    let μ := min (normalMass s) (1-normalMass s)
    MemLp (edgeImagTrace s γ u) 2 volume ∧
      (∫ x, edgeImagTrace s γ u x^2)/π≤(2^15/μ)^2 := by
  let a := normalMass s
  let μ := min a (1-a)
  let f := fun z : ℂ => (crossSource a (direction γ) z).im
  have hf : Measurable f := Complex.measurable_im.comp (measurable_crossSource ..)
  have hμ : 0<μ := lt_min (Certificate.normalMass_pos _) (by dsimp [a]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _)
  have hμ₁ : μ≤1 := (min_le_right ..).trans (by linarith [show 0<a from Certificate.normalMass_pos _])
  have hsep (z : ℂ) (hz : 0<z.im) := edge_source_separated_feet (s:=s) hg hc hz
  have hcore (z : ℂ) (hz : 0<z.im) (_ : ‖z‖≤4) : |f z|≤128/‖z‖ ∨
      (‖z-(cos γ:ℂ)‖≤4 ∧ |f z|≤128/‖z-(cos γ:ℂ)‖) ∨ |f z|≤2048/μ := by
    by_cases h₁ : ‖z‖<μ*cos γ/8
    · exact Or.inl ((Complex.abs_im_le_norm _).trans (((hsep z hz).1 h₁).2))
    by_cases h₂ : ‖z-(cos γ:ℂ)‖<μ*cos γ/8
    · have hμc := mul_le_mul_of_nonneg_left (cos_le_one γ) hμ.le
      exact Or.inr (Or.inl ⟨by linarith, (Complex.abs_im_le_norm _).trans (((hsep z hz).2.1 h₂).2)⟩)
    exact Or.inr (Or.inr ((Complex.abs_im_le_norm _).trans ((hsep z hz).2.2.1 (le_of_not_gt h₁) (le_of_not_gt h₂))))
  have hfar (z : ℂ) (hz : 0<z.im) (hr : 4<‖z‖) : |f z|≤4/‖z‖^4 :=
    (Complex.abs_im_le_norm _).trans ((hsep z hz).2.2.2 (by linarith))
  obtain ⟨hi,hbound⟩ := edge_imag_weighted_area hf (cos γ) (by norm_num) (by norm_num)
    (show 0≤2048/μ by positivity) hcore hfar
  obtain ⟨hL,hv⟩ := depthPoissonReal_sq_of_area hf hu hi
  refine ⟨hL,hv.trans ((mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ)≤5)).trans ?_)⟩
  change 5*(4*128^2+4*128^2+16*(2048/μ)^2+1)≤((2:ℝ)^15/μ)^2
  rw [div_pow,div_pow]
  field_simp [hμ.ne']
  nlinarith only [pow_le_pow_left₀ hμ.le hμ₁ 2]

/-- E.3(b) includes membership of the actual zero-depth imaginary trace in
L². The magnitude is bounded uniformly by 16/sin³ γ. -/
theorem edge_imag_trace_fixed {s γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hσ : 0<sin γ)
    (hu : 0≤u) :
    MemLp (edgeImagTrace s γ u) 2 volume ∧
      (∫ x, edgeImagTrace s γ u x^2)/π≤(16/sin γ^3)^2 := by
  let a := normalMass s
  let b := 1-a
  let f := fun z : ℂ => (crossSource a (direction γ) z).im
  have hf : Measurable f := Complex.measurable_im.comp (measurable_crossSource ..)
  have hb : 0<b := by dsimp [b,a]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _
  have hb₁ : b≤1 := by dsimp [b]; linarith [show 0<a from Certificate.normalMass_pos _]
  have hs (z : ℂ) (hz : 0<z.im) := edge_source_fixed_angle (s:=s) hg hσ hz
  have hcore (z : ℂ) (hz : 0<z.im) (_ : ‖z‖≤4) : |f z|≤(2*b/sin γ^3)/‖z‖ ∨
      (‖z-(0:ℂ)‖≤4 ∧ |f z|≤0/‖z-(0:ℂ)‖) ∨ |f z|≤0 := by
    apply Or.inl
    apply ((Complex.abs_im_le_norm _).trans ((hs z hz).2.1)).trans_eq
    rw [div_div,mul_comm (sin γ^3)]
  have hfar (z : ℂ) (hz : 0<z.im) (hr : 4<‖z‖) : |f z|≤4/‖z‖^4 :=
    (Complex.abs_im_le_norm _).trans ((hs z hz).2.2 (by linarith))
  obtain ⟨hi,hbound⟩ := edge_imag_weighted_area hf 0 (K₁:=2*b/sin γ^3) (by positivity) (le_refl 0) (le_refl 0)
    (by simpa only [Complex.ofReal_zero] using hcore) hfar
  obtain ⟨hL,hv⟩ := depthPoissonReal_sq_of_area hf hu hi
  refine ⟨hL,hv.trans ((mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ)≤5)).trans ?_)⟩
  change 5*(4*(2*b/sin γ^3)^2+4*0^2+16*0^2+1)≤(16/sin γ^3)^2
  field_simp [hσ.ne']
  nlinarith only [pow_le_pow_left₀ hb.le hb₁ 2,pow_le_pow_left₀ hσ.le (sin_le_one γ) 6]

end Liu
