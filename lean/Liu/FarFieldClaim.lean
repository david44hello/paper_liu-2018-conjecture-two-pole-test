import Liu.FarGradient
import Liu.FinitePartLaws

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology
namespace Liu

private theorem polarRay_deriv (R x : ℝ) :
    HasDerivAt (polarRay R) (Complex.I*polarRay R x) x := by
  have h := ((hasDerivAt_id (x:ℂ)).mul_const Complex.I).cexp.comp_ofReal
  unfold polarRay unitPhase
  convert h.const_mul (R:ℂ) using 1
  · rfl
  · simp [id_eq]; ring

private theorem polarRay_height {R θ : ℝ} (hR : 0≤R) (hθ : θ∈Icc 0 π) : 0≤(polarRay R θ).im := by
  have hi : (polarRay R θ).im=R*sin θ := by simp [polarRay,unitPhase,Complex.exp_mul_I,←Complex.ofReal_sin,←Complex.ofReal_cos]
  rw [hi]; exact mul_nonneg hR (sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)

theorem PickSum.potential_far_estimate {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → 1<‖z‖ →
      ‖potential p.value z-angularPotential p.mass z‖ ≤ C*(1+log ‖z‖)/‖z‖ := by
  obtain ⟨K,hK,hgrad⟩ := p.gradient_far_estimate
  refine ⟨π*K,by positivity,?_⟩
  intro z hz hr
  let R := ‖z‖
  have hR : 0<R := zero_lt_one.trans hr
  let Q := fun w => potential p.value w-angularPotential p.mass w
  let F := fun a : ℝ => Q (polarRay R a)
  have hn (a : ℝ) : ‖polarRay R a‖=R := by rw [polarRay,norm_mul,Complex.norm_of_nonneg hR.le,unitPhase_norm,mul_one]
  have dr (a : ℝ) (ha : a∈Icc 0 π) : DifferentiableAt ℝ Q (polarRay R a) :=
    (p.potential_hasFDerivAt_closed (polarRay_height hR.le ha)).differentiableAt.sub
      (angularPotential_hasFDerivAt p.mass (polarRay_height hR.le ha) (norm_ne_zero_iff.mp ((hn a).symm ▸ hR.ne'))).differentiableAt
  have hd (a : ℝ) (ha : a∈Icc 0 π) := (dr a ha).hasFDerivAt.comp_hasDerivAt a (polarRay_deriv R a)
  have hbound (a : ℝ) (ha : a∈Icc 0 π) : ‖deriv F a‖ ≤ K*(1+log R)/R := by
    have h := hd a ha
    change HasDerivAt F _ a at h; rw [h.deriv]
    apply ((fderiv ℝ Q (polarRay R a)).le_opNorm _).trans
    rw [norm_mul,Complex.norm_I,one_mul,hn]
    have hg := hgrad (polarRay R a) (polarRay_height hR.le ha) ((hn a).symm ▸ hr)
    rw [hn] at hg
    apply (mul_le_mul_of_nonneg_right hg hR.le).trans_eq
    field_simp [hR.ne']
  have h0 : F 0=0 := by
    change potential p.value (polarRay R 0)-angularPotential p.mass (polarRay R 0)=0
    rw [show polarRay R 0=(R:ℂ) by simp [polarRay,unitPhase],potential_boundary,
      angularPotential_eq _ (by simp) (Complex.ofReal_ne_zero.mpr hR.ne'),Complex.arg_ofReal_of_nonneg hR.le]
    simp
  have hθ := Complex.arg_nonneg_iff.mpr hz
  have hθπ := Complex.arg_le_pi z
  have hh := (convex_Icc (0:ℝ) π).norm_image_sub_le_of_norm_deriv_le
    (f:=F) (fun a ha => (hd a ha).differentiableAt) hbound (left_mem_Icc.mpr pi_pos.le) ⟨hθ,hθπ⟩
  rw [h0,sub_zero,sub_zero,Real.norm_eq_abs,abs_of_nonneg hθ] at hh
  change ‖Q (polarRay R z.arg)‖ ≤ _ at hh
  rw [show polarRay R z.arg=z from Complex.norm_mul_exp_arg_mul_I z] at hh
  apply hh.trans
  have hl := log_nonneg hr.le
  apply (mul_le_mul_of_nonneg_left hθπ (by change 0≤K*(1+log ‖z‖)/‖z‖; positivity)).trans_eq
  ring

/-- Uniform potential, full real gradient and field estimates of Lemma 2.3
on the closed half-plane, with a smooth extension for the angular model. -/
theorem PickSum.far_field {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ z : ℂ, 0≤z.im → 1<‖z‖ →
      ‖potential p.value z-Complex.I*((p.mass/2*z.arg*(π-z.arg):ℝ):ℂ)‖ ≤ C*(1+log ‖z‖)/‖z‖ ∧
      ‖fderiv ℝ (fun w => potential p.value w-angularPotential p.mass w) z‖ ≤ C*(1+log ‖z‖)/‖z‖^2 ∧
      ‖field p.value z-fieldFarModel p.mass z‖ ≤ C*(1+log ‖z‖)/‖z‖^2 := by
  obtain ⟨A,hA,ha⟩ := p.potential_far_estimate
  obtain ⟨B,hB,hb⟩ := p.gradient_far_estimate
  obtain ⟨D,hD,hd⟩ := p.field_far_estimate
  refine ⟨A+B+D,by positivity,?_⟩
  intro z hz hr
  have hn := norm_pos_iff.mp (zero_lt_one.trans hr)
  have hl := log_nonneg hr.le
  rw [←angularPotential_eq p.mass hz hn]
  refine ⟨(ha z hz hr).trans ?_,(hb z hz hr).trans ?_,(hd z hz hr).trans ?_⟩ <;>
    apply div_le_div_of_nonneg_right _ (by positivity) <;> apply mul_le_mul_of_nonneg_right _ (by linarith) <;> linarith

end Liu
