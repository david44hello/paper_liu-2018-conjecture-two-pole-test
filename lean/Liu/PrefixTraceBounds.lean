import Liu.EdgeTraceEstimates

noncomputable section
open Set Real MeasureTheory
namespace Liu

theorem physical_angle_split {γ : ℝ} (hg : γ∈Icc 0 (π/2)) : 1/2≤ cos γ ∨ 1/2≤ sin γ := by
  have hc := cos_nonneg_of_mem_Icc (show γ∈Icc (-(π/2)) (π/2) from ⟨by linarith [hg.1,pi_pos],hg.2⟩)
  have hs := sin_nonneg_of_nonneg_of_le_pi hg.1 (hg.2.trans (by linarith [pi_pos]))
  by_contra! hn
  nlinarith only [pow_le_pow_left₀ hc hn.1.le 2,pow_le_pow_left₀ hs hn.2.le 2,sin_sq_add_cos_sq γ]

theorem uniform_edge_norms (s : ℝ) {γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0≤u) :
    let C := 2^15/Certificate.smallMass s
    let c := edgeRealTrace s γ u
    let q := edgeImagTrace s γ u
    Integrable c ∧ (∫ x, |c x|)/π≤C ∧ (∀ x, |c x|≤5*C) ∧
      MemLp q 2 volume ∧ (∫ x, q x^2)/π≤C^2 := by
  rcases physical_angle_split hg with hc|hs
  · obtain ⟨hi,h₁,hsup⟩ := edge_real_trace_separated (s:=s) hg hc hu
    obtain ⟨hm,hq⟩ := edge_imag_trace_separated (s:=s) hg hc hu
    exact ⟨hi,h₁,hsup,hm,hq⟩
  · let a := normalMass s
    let μ := Certificate.smallMass s
    have ha : 0<a := Certificate.normalMass_pos _
    have hμ : 0<μ := lt_min ha (by rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _)
    have hμa : μ≤a := min_le_left .. 
    have hμ₁ : μ≤1 := (min_le_right ..).trans (by linarith [Certificate.normalMass_pos s])
    have hσ : 0<sin γ := by linarith
    obtain ⟨hi,h₁,hsup⟩ := edge_real_trace_fixed (s:=s) hg hσ hu
    obtain ⟨hm,hq⟩ := edge_imag_trace_fixed (s:=s) hg hσ hu
    have hC : 8/(a*sin γ^4)≤2^15/μ := by
      apply (div_le_div_iff₀ (by positivity) hμ).mpr
      nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hs 4) ha.le,hμa,ha]
    have hM : 16/sin γ^3≤2^15/μ := by
      apply (div_le_div_iff₀ (by positivity) hμ).mpr
      nlinarith only [pow_le_pow_left₀ (by norm_num) hs 3,hμ₁]
    exact ⟨hi,h₁.trans hC,fun x => (hsup x).trans (by
      change 3*(8/(a*sin γ^4))≤5*(2^15/μ)
      linarith [show 0≤(2:ℝ)^15/μ by positivity]),hm,hq.trans (pow_le_pow_left₀ (by positivity) hM 2)⟩

/-- At least one pole trace is bounded at every boundary point, uniformly over
all physical angles, including coincident real projections. -/
theorem isolated_min_bound {s γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0<u) (x : ℝ) :
    let A := normalMass s*isolatedTrace 0 u x
    let B := (1-normalMass s)*isolatedTrace (cos γ) (sin γ+u) x
    A≤8 ∨ B≤8 := by
  let a := normalMass s
  let b := 1-a
  have ha : 0<a := Certificate.normalMass_pos _
  have hb : 0<b := by dsimp [a,b]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _
  have ha₁ : a≤1 := by dsimp [b] at hb; linarith
  have hb₁ : b≤1 := by dsimp [b]; linarith
  have hs := sin_nonneg_of_nonneg_of_le_pi hg.1 (hg.2.trans (by linarith [pi_pos]))
  have hv := add_pos_of_nonneg_of_pos hs hu
  have hsep (m c d : ℝ) (hm : 0 < m) (hm₁ : m≤1) (hd : 0<d) (hx : 1/4≤|x-c|) :
      m*isolatedTrace c d x≤8 := by
    have hdist : 0 < |x-c| := by linarith
    apply (mul_le_mul_of_nonneg_left (isolatedTrace_le_distance c x hd (sub_ne_zero.mp (abs_pos.mp hdist))) hm.le).trans
    rw [←mul_div_assoc,div_le_iff₀ (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hm₁ pi_pos.le,pi_lt_four,hx]
  rcases physical_angle_split hg with hc|hs'
  · by_cases hx : 1/4≤|x-(0:ℝ)|
    · exact Or.inl (hsep a 0 u ha ha₁ hu hx)
    · apply Or.inr (hsep b (cos γ) (sin γ+u) hb hb₁ hv ?_)
      have h := abs_sub_le (cos γ) x 0
      rw [sub_zero,abs_of_nonneg (by linarith : 0≤ cos γ),abs_sub_comm (cos γ) x] at h
      linarith
  · apply Or.inr
    apply (mul_le_mul_of_nonneg_left (isolatedTrace_le_depth (cos γ) x hv) hb.le).trans
    rw [mul_one_div,div_le_iff₀ hv]; linarith

end Liu
