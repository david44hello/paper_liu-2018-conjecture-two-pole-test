import Liu.IsolatedMoment

noncomputable section
open Set Real MeasureTheory
namespace Liu

/-- Perturbing the argument of a lower-pole resolvent gives simultaneous
spatial and height bounds for the associated Poisson kernel. -/
private theorem poisson_change {a x x' t h : ℝ} (ht : 0<t) (hh : 0≤h) :
    |poissonLine a (t+h) x'-poissonLine a t x|≤(|x'-x|+h)/t^2 := by
  let z : ℂ := ((x'-a:ℝ):ℂ)+((t+h:ℝ):ℂ)*Complex.I
  let w : ℂ := ((x-a:ℝ):ℂ)+(t:ℂ)*Complex.I
  have ht' : 0<t+h := by linarith
  have hz : t+h≤‖z‖ := by simpa [z] using Complex.im_le_norm z
  have hw : t≤‖w‖ := by simpa [w] using Complex.im_le_norm w
  have hnz := norm_pos_iff.mp (ht'.trans_le hz)
  have hnw := norm_pos_iff.mp (ht.trans_le hw)
  have hdiff : w-z=((x-x':ℝ):ℂ)-(h:ℂ)*Complex.I := by dsimp [z,w]; push_cast; ring
  have hnorm : ‖w-z‖≤|x'-x|+h := by
    rw [hdiff]
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,abs_of_nonneg hh,abs_sub_comm x x'] using
      norm_sub_le ((x-x':ℝ):ℂ) ((h:ℂ)*Complex.I)
  rw [poissonLine_of_resolvent,poissonLine_of_resolvent]
  change |-z⁻¹.im- -w⁻¹.im|≤_
  rw [show -z⁻¹.im- -w⁻¹.im= -(z⁻¹-w⁻¹).im by simp only [Complex.sub_im]; ring,abs_neg]
  apply (Complex.abs_im_le_norm _).trans
  have e : z⁻¹-w⁻¹=(w-z)/(z*w) := by field_simp [hnz,hnw]
  rw [e,norm_div,norm_mul]
  apply div_le_div₀ (by positivity) hnorm (sq_pos_of_pos ht)
  simpa [pow_two] using mul_le_mul (show t≤‖z‖ by linarith) hw ht.le (norm_nonneg _)

private theorem isolated_slice_integrable (a x : ℝ) {d : ℝ} (hd : 0<d) :
    IntegrableOn (fun t => poissonLine a t x/(t+d)) (Ioi d) := by
  apply (integrableOn_Ioi_rpow_of_lt (a:=(-2:ℝ)) (by norm_num) hd).mono'
    ((show Measurable (fun t : ℝ => poissonLine a t x/(t+d)) by unfold poissonLine; fun_prop).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=d))] with t ht
  have ht₀ := hd.trans ht
  have den : 0<(x-a)^2+t^2 := by positivity
  have hsum : 0<t+d := by positivity
  rw [Real.norm_of_nonneg (by unfold poissonLine; positivity : 0≤poissonLine a t x/(t+d)),
    poissonLine,div_div,rpow_neg ht₀.le,rpow_ofNat,←one_div,div_le_div_iff₀ (mul_pos den hsum) (sq_pos_of_pos ht₀)]
  nlinarith [mul_nonneg (sq_nonneg (x-a)) hsum.le,mul_nonneg (sq_nonneg t) hd.le]

/-- At positive depth the isolated trace varies at most linearly in the
horizontal position and in an additional downward shift. -/
theorem isolatedTrace_stability (a x x' : ℝ) {d h : ℝ} (hd : 0<d) (hh : 0≤h) :
    |isolatedTrace a (d+h) x'-isolatedTrace a d x| ≤ (|x'-x|+3*h)/(2*d^2) := by
  have hdh := add_pos_of_pos_of_nonneg hd hh
  let f := fun t : ℝ => poissonLine a t x'/(t+(d+h))
  let F := fun t : ℝ => f (t+h)
  let G := fun t : ℝ => poissonLine a t x/(t+d)
  have hs := measurePreserving_add_right (volume:Measure ℝ) h
  have hpre : (fun t : ℝ => t+h) ⁻¹' Ioi (d+h) = Ioi d := by ext t; simp
  have hFI : IntegrableOn F (Ioi d) := by
    rw [←hpre]; exact (hs.integrableOn_comp_preimage (Homeomorph.addRight h).measurableEmbedding).mpr
      (isolated_slice_integrable a x' hdh)
  have hGI : IntegrableOn G (Ioi d) := isolated_slice_integrable a x hd
  have hrepr : isolatedTrace a (d+h) x'=∫ t in Ioi d, F t := by
    rw [←hpre]; exact (hs.setIntegral_preimage_emb (Homeomorph.addRight h).measurableEmbedding f (Ioi (d+h))).symm
  rw [hrepr,show isolatedTrace a d x=∫ t in Ioi d, G t from rfl,←integral_sub hFI hGI,←Real.norm_eq_abs]
  let D := |x'-x|+3*h
  have hDi := (integrableOn_Ioi_rpow_of_lt (a:=(-3:ℝ)) (by norm_num) hd).const_mul D
  apply (norm_integral_le_of_norm_le hDi ?_).trans_eq
  · rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num) hd]
    norm_num [rpow_neg hd.le]; ring
  · filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=d))] with t ht
    have ht₀ := hd.trans ht
    have htt : 0<t+h := by linarith
    let v := t+d
    let w := t+h+(d+h)
    let p := poissonLine a (t+h) x'
    let q := poissonLine a t x
    have hv : t≤v := by dsimp [v]; linarith
    have hw : t≤w := by dsimp [w]; linarith
    have hv₀ := ht₀.trans_le hv
    have hw₀ := ht₀.trans_le hw
    have hwv : w-v=2*h := by dsimp [w,v]; ring
    have hq : 0≤q := by dsimp [q,poissonLine]; positivity
    have hq' : q≤1/t := by
      change t/((x-a)^2+t^2)≤1/t
      rw [div_le_div_iff₀ (by positivity) ht₀]; nlinarith [sq_nonneg (x-a)]
    have h₁ : |(p-q)/w|≤(|x'-x|+h)/t^3 := by
      rw [abs_div,abs_of_pos hw₀,show t^3=t^2*t by ring,←div_div]
      exact div_le_div₀ (by positivity) (poisson_change (a:=a) ht₀ hh) ht₀ hw
    have h₂ : |q*(1/w-1/v)|≤2*h/t^3 := by
      have he : 1/w-1/v= -(2*h/(v*w)) := by rw [←hwv]; field_simp [hv₀.ne',hw₀.ne']; ring
      rw [he,abs_mul,abs_of_nonneg hq,abs_neg,abs_of_nonneg (by positivity : 0≤2*h/(v*w))]
      have hh' := div_le_div_of_nonneg_left (show 0≤2*h by positivity) (sq_pos_of_pos ht₀)
        (show t^2≤v*w by simpa [sq] using mul_le_mul hv hw ht₀.le hv₀.le)
      exact (mul_le_mul hq' hh' (by positivity) (by positivity)).trans_eq (by ring)
    change ‖p/w-q/v‖≤D*t^(-(3:ℝ))
    rw [Real.norm_eq_abs,show p/w-q/v=(p-q)/w+q*(1/w-1/v) by ring]
    apply (abs_add_le ..).trans ((add_le_add h₁ h₂).trans_eq ?_)
    rw [rpow_neg ht₀.le,rpow_ofNat]; dsimp [D]; ring

end Liu
