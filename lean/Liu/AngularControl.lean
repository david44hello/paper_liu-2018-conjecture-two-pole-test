import Liu.AngularEndpoint
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

noncomputable section
open Set Real
open scoped Topology
namespace Liu

/-- An elementary Dirichlet estimate for complex values. Rolle's theorem is applied
to the real and imaginary components separately. -/
private theorem angular_dirichlet_estimate {y v : ℝ → ℂ} {K : ℝ} (hK : 0≤K)
    (dy : ∀ x, HasDerivAt y (v x) x) (dv : Differentiable ℝ v)
    (lo : y 0=0) (hi : y π=0) (h : ∀ x∈Icc 0 π, ‖deriv v x‖≤K) :
    ∀ x∈Icc 0 π, ‖v x‖≤2*π*K ∧ ‖y x‖≤2*π^2*K := by
  have hvc (x u : ℝ) (hx : x∈Icc 0 π) (hu : u∈Icc 0 π) : ‖v x-v u‖≤K*π := by
    apply ((convex_Icc (0:ℝ) π).norm_image_sub_le_of_norm_deriv_le (fun z _ => dv z) h hu hx).trans
    rw [Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hx.1,hu.2],by linarith [hu.1,hx.2]⟩) hK
  have comp (L : ℂ →L[ℝ] ℝ) (x : ℝ) : HasDerivAt (fun u => L (y u)) (L (v x)) x :=
    L.hasFDerivAt.comp_hasDerivAt x (dy x)
  have hpoint (L : ℂ →L[ℝ] ℝ) : ∃ u∈Icc 0 π, L (v u)=0 := by
    have hd (x : ℝ) := comp L x
    obtain ⟨u,hu,hzero⟩ := exists_deriv_eq_zero pi_pos (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (show L (y 0)=L (y π) by rw [lo,hi])
    exact ⟨u,⟨hu.1.le,hu.2.le⟩,(hd u).deriv.symm.trans hzero⟩
  obtain ⟨u,hu,hU⟩ := hpoint Complex.reCLM
  obtain ⟨w,hw,hW⟩ := hpoint Complex.imCLM
  change (v u).re=0 at hU
  change (v w).im=0 at hW
  have hv x (hx : x∈Icc 0 π) : ‖v x‖≤2*π*K := by
    have hr := (Complex.abs_re_le_norm (v x-v u)).trans (hvc x u hx hu)
    have hi := (Complex.abs_im_le_norm (v x-v w)).trans (hvc x w hx hw)
    simp only [Complex.sub_re,hU,sub_zero] at hr
    simp only [Complex.sub_im,hW,sub_zero] at hi
    linarith [Complex.norm_le_abs_re_add_abs_im (v x)]
  intro x hx
  refine ⟨hv x hx,?_⟩
  have hy := (convex_Icc (0:ℝ) π).norm_image_sub_le_of_norm_deriv_le
    (fun u _ => (dy u).differentiableAt) (fun u hu => (dy u).deriv ▸ hv u hu) (left_mem_Icc.mpr pi_pos.le) hx
  rw [lo,sub_zero,sub_zero,Real.norm_eq_abs,abs_of_nonneg hx.1] at hy
  exact hy.trans ((mul_le_mul_of_nonneg_left hx.2 (by positivity : 0≤2*π*K)).trans_eq (by ring))

/-- Bounds uniform down to the angular endpoint for the Dirichlet solution and
its angular derivative. -/
theorem angularSolution_uniform_bounds {t : ℝ} (ht : 0<t) (ht1 : t<1) (hsmall : t*π≤1/2) :
    ∀ x∈Icc 0 π, ‖angularSolution t x‖≤8*π^2 ∧
      ‖deriv (fun u : ℝ => angularSolution t u) x‖≤8*π := by
  let y := fun u : ℝ => angularSolution t u
  obtain ⟨v,hv⟩ := angularSolution_real_system ht ht1
  have dy (x : ℝ) : HasDerivAt y (v x) x := (hv x).1
  have dv : Differentiable ℝ v := fun x => (hv x).2.differentiableAt
  obtain ⟨u,hu,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr pi_pos.le)
    (show ContinuousOn (fun x => ‖y x‖) (Icc 0 π) from fun x _ => (dy x).continuousAt.norm.continuousWithinAt)
  let M := ‖y u‖
  have hM : 0≤M := norm_nonneg _
  have bounds (x : ℝ) (hx : x∈Icc 0 π) : ‖deriv v x‖≤2+t^2*M := by
    rw [(hv x).2.deriv]
    apply (norm_sub_le ..).trans
    have he : ‖Complex.exp ((t:ℂ)*(x:ℂ)*Complex.I)‖=1 := by simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
    simp only [norm_mul,norm_pow,Complex.norm_of_nonneg ht.le,Complex.norm_of_nonneg (by linarith : 0≤1+t),he,mul_one]
    exact add_le_add (by linarith) (mul_le_mul_of_nonneg_left (hmax hx) (sq_nonneg _))
  obtain ⟨hl,hr,_⟩ := angularSolution_dirichlet ht ht1
  have hh := angular_dirichlet_estimate (by positivity : 0≤2+t^2*M) dy dv (by simpa [y] using hl) hr bounds
  have hs := pow_le_pow_left₀ (mul_nonneg ht.le pi_pos.le) hsmall 2
  have hsq : π^2*t^2≤1/4 := by nlinarith only [hs]
  have hMu : M ≤ 8*π^2 := by
    have h' := (hh u hu).2
    change M≤_ at h'
    nlinarith only [h',mul_le_mul_of_nonneg_right hsq hM]
  have hforce : 2+t^2*M≤4 := by nlinarith only [mul_le_mul_of_nonneg_left hMu (sq_nonneg t),hsq]
  intro x hx
  refine ⟨(hmax hx).trans hMu,?_⟩
  rw [(dy x).deriv]
  exact ((hh x hx).1.trans (mul_le_mul_of_nonneg_left hforce (by positivity))).trans_eq (by ring)

end Liu
