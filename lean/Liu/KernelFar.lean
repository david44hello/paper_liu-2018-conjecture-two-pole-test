import Liu.KernelControl

noncomputable section
open Set MeasureTheory Metric Real
open scoped ComplexConjugate
namespace Liu

/-- After scaling the plane by 1+|z|, the far contribution is dominated by one
fixed integrable radial function. The estimate holds uniformly down to the real axis. -/
theorem PickSum.residual_far_bound {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0<t) :
    ∃ C > 0, ∀ z v : ℂ, z ∈ upper → v ∈ upper →
      let R := 1+‖z‖
      let w := R • v
      R/2 ≤ ‖w-z‖ → ‖residualIntegrand (p.power t) z w‖ ≤
        C*(1+log R)/(R^t*R^2)*radialWeight t v := by
  obtain ⟨B,hB,hlog⟩ := p.log_power_growth ht
  obtain ⟨_,_,hscale⟩ := p.power_two_sided ht.le
  let U := p.bound^t
  have hU : 0<U := rpow_pos_of_pos p.bound_pos _
  let A := 2*B+2*t+1
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨25*U*A,by positivity,?_⟩
  intro z v hz hv
  dsimp only
  let R := 1+‖z‖
  let w := R • v
  change R/2 ≤ ‖w-z‖ → ‖residualIntegrand (p.power t) z w‖ ≤ _
  intro hfar
  have hR : 1≤R := by dsimp [R]; linarith [norm_nonneg z]
  have hRp := zero_lt_one.trans_le hR
  have hℓ := log_nonneg hR
  have hn : ‖w‖=R*‖v‖ := by simp [w,norm_smul,abs_of_pos hRp]
  have hw : w ∈ upper := by change 0<(R • v).im; simpa [Complex.real_smul,hRp] using (show 0 < v.im from hv)
  have hvp : 0<‖v‖ := norm_pos_iff.mpr (fun he => by change 0<v.im at hv; simp [he] at hv)
  have hwp : 0<‖w‖ := hn.symm ▸ mul_pos hRp hvp
  have D := (hscale w (le_of_lt hw)).2
  have hF : ‖p.power t w‖ ≤ U/(R^t*‖v‖^t) := by
    apply D.trans
    rw [←mul_rpow hRp.le hvp.le,←hn]
    apply div_le_div_of_nonneg_left hU.le (rpow_pos_of_pos hwp t)
    exact rpow_le_rpow hwp.le (by linarith) ht.le
  have hlogR := (hlog z (le_of_lt hz)).1
  have hlogW := (hlog w (le_of_lt hw)).1
  have hplus : log (1+‖w‖) ≤ log R+‖v‖ := by
    have h := log_le_log (by positivity : 0<1+‖w‖) (show 1+‖w‖ ≤ R*(1+‖v‖) by rw [hn]; nlinarith)
    rw [log_mul hRp.ne' (by positivity)] at h
    linarith [log_le_sub_one_of_pos (x:=1+‖v‖) (by positivity)]
  have hlogD : |log ‖p.power t z‖-log ‖p.power t w‖| ≤ A*(1+log R)*(1+‖v‖) := by
    have hh := abs_sub_le (log ‖p.power t z‖) 0 (log ‖p.power t w‖)
    rw [sub_zero,zero_sub,abs_neg] at hh
    have hu : |log ‖p.power t z‖-log ‖p.power t w‖| ≤ 2*B+2*t*log R+t*‖v‖ := by
      change _ ≤ B+t*log R at hlogR
      linarith [mul_le_mul_of_nonneg_left hplus ht.le]
    apply hu.trans
    have h1 : 2*B ≤ A := by dsimp [A]; linarith
    have h2 : 2*t ≤ A := by dsimp [A]; linarith
    have h3 : t ≤ A := by dsimp [A]; linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hℓ,mul_le_mul_of_nonneg_right h3 (norm_nonneg v),
      mul_nonneg (mul_nonneg hA.le hℓ) (norm_nonneg v)]
  have hgeom : R*(1+‖v‖) ≤ 5*‖w-conj z‖ := by
    have h := norm_add_le (w-z) z
    rw [sub_add_cancel] at h
    have hh := distance_to_reflection_bound z w (le_of_lt hz) (le_of_lt hw)
    have hzr : ‖z‖ ≤ R := by dsimp [R]; linarith
    nlinarith
  have hpos : 0<‖w-conj z‖ := by nlinarith [mul_pos hRp (by positivity : 0<1+‖v‖)]
  have hgeom' : 1/‖w-conj z‖^2 ≤ 25/(R^2*(1+‖v‖)^2) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hpos) (by positivity)).mpr
    have h := pow_le_pow_left₀ (mul_nonneg hRp.le (by positivity : 0≤1+‖v‖)) hgeom 2
    nlinarith
  rw [integrand_norm,div_eq_mul_one_div]
  calc
    _ ≤ ((U/(R^t*‖v‖^t))*(A*(1+log R)*(1+‖v‖)))*(25/(R^2*(1+‖v‖)^2)) :=
      mul_le_mul (mul_le_mul hF hlogD (abs_nonneg _) (by positivity)) hgeom' (by positivity) (by positivity)
    _ = _ := by
      change _ = 25*U*A*(1+log R)/(R^t*R^2)*radialWeight t v
      rw [radialWeight,rpow_neg hvp.le]
      field_simp [hRp.ne',(rpow_pos_of_pos hRp t).ne',(rpow_pos_of_pos hvp t).ne',show 1+‖v‖ ≠ 0 by positivity]
      <;> ring

end Liu
