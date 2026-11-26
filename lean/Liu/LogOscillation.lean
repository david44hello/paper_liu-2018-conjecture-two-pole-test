import Liu.LogSource
import Liu.GreenBoundary

noncomputable section
open Set MeasureTheory Metric Real
namespace Liu

theorem PickSum.logDerivative_decay {n : ℕ} (p : PickSum n) :
    ∃ L > 0, ∀ z : ℂ, 0 ≤ z.im → ‖deriv p.value z / p.value z‖ ≤ L/(1+‖z‖) := by
  obtain ⟨c,hc,hp⟩ := p.two_sided_decay
  have hD : 0 ≤ p.derivativeBound/2 := by
    simpa using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  let L := (1+p.derivativeBound)/c
  refine ⟨L,div_pos (by linarith) hc,?_⟩
  intro z hz
  have hV : p.value z ≠ 0 := fun he => by have hi := p.value_im_pos hz; simp [he] at hi
  have hd := p.source_decay hz
  rw [source_norm hV] at hd
  have hR : 0<1+‖z‖ := by positivity
  have hs := (le_div_iff₀ (sq_pos_of_pos hR)).mp hd
  have hlow := (div_le_iff₀ hR).mp (hp z hz).1
  have hv := norm_pos_iff.mpr hV
  rw [norm_div,div_div,div_le_div_iff₀ hv (mul_pos hc hR)]
  have hbound : ‖deriv p.value z‖*(1+‖z‖)^2 ≤ p.derivativeBound := by linarith
  have hbound' := mul_le_mul_of_nonneg_right hbound hv.le
  have hscale := mul_le_mul_of_nonneg_left hlow (mul_nonneg (norm_nonneg (deriv p.value z)) hR.le)
  nlinarith

theorem PickSum.log_power_oscillation {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0<t) :
    ∃ L > 0, ∀ z w : ℂ, 0 ≤ z.im → 0 ≤ w.im → ‖w-z‖ ≤ (1+‖z‖)/2 →
    |log ‖p.power t w‖-log ‖p.power t z‖| ≤ L*‖w-z‖/(1+‖z‖) := by
  obtain ⟨D,hD,hb⟩ := p.logDerivative_decay
  refine ⟨2*t*D,by positivity,?_⟩
  intro z w hz hw hnear
  let R := 1+‖z‖
  let K := closedBall z (R/2) ∩ {u : ℂ | 0 ≤ u.im}
  have hR : 0<R := by dsimp [R]; positivity
  have hK : Convex ℝ K := (convex_closedBall z (R/2)).inter (convex_Ici (0:ℝ) |>.linear_preimage Complex.imCLM.toLinearMap)
  have hder (u : ℂ) (hu : u ∈ K) : HasDerivAt (fun v => Complex.log (p.value v)) (deriv p.value u / p.value u) u :=
    (p.hasDerivAt hu.2).differentiableAt.hasDerivAt.clog
      (Complex.mem_slitPlane_iff.mpr (Or.inr (p.value_im_pos hu.2).ne'))
  have hbound (u : ℂ) (hu : u ∈ K) : ‖deriv (fun v => Complex.log (p.value v)) u‖ ≤ 2*D/R := by
    rw [(hder u hu).deriv]
    apply (hb u hu.2).trans
    have hδ : ‖z-u‖ ≤ R/2 := by simpa [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev u z] using hu.1
    have hrad : R ≤ 2*(1+‖u‖) := by dsimp [R] at *; have hh := norm_add_le (z-u) u; rw [sub_add_cancel] at hh; linarith
    apply (div_le_div_iff₀ (by positivity) hR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hrad hD.le]
  have hzw := hK.norm_image_sub_le_of_norm_deriv_le (fun u hu => (hder u hu).differentiableAt) hbound
    (show z ∈ K from ⟨mem_closedBall_self (by positivity),hz⟩) (show w ∈ K from ⟨by simpa [dist_eq_norm] using hnear,hw⟩)
  have hre := Complex.abs_re_le_norm (Complex.log (p.value w)-Complex.log (p.value z))
  simp only [Complex.sub_re,Complex.log_re] at hre
  have hn (u : ℂ) (hu : 0≤u.im) : 0<‖p.value u‖ := norm_pos_iff.mpr (fun he => by
    have hh := p.value_im_pos hu; simp [he] at hh)
  simp only [PickSum.power,Complex.norm_cpow_real,log_rpow (hn w hw),log_rpow (hn z hz),
    ←mul_sub,abs_mul,abs_of_pos ht]
  calc
    _ ≤ t*((2*D/R)*‖w-z‖) := mul_le_mul_of_nonneg_left (hre.trans hzw) ht.le
    _ = _ := by dsimp [R]; ring

end Liu
