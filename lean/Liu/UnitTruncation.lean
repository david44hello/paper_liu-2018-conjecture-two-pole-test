import Liu.FirstOrderExpansion
import Liu.PoissonLine

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped Topology ComplexConjugate
namespace Liu

private def bulkTail (r : ℝ) := (Ioi (16:ℝ)).indicator (fun t => t^(-(5/2:ℝ))) r
private def stripWeight (z : ℂ) := (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) z.im*poissonLine 0 1 z.re

private theorem bulkTail_integral :
    Integrable (fun z : ℂ => bulkTail ‖z‖) upperArea ∧
    (∫ z : ℂ, bulkTail ‖z‖ ∂upperArea) = 1/2 := by
  have hi : (∫ z : ℂ, bulkTail ‖z‖ ∂upperArea) = 1/2 := by
    rw [upperArea_radial]
    have he (r : ℝ) (hr : r∈Ioi (0:ℝ)) : r*bulkTail r =
        (Ioi (16:ℝ)).indicator (fun t => t^(-(3/2:ℝ))) r := by
      by_cases h : 16<r
      · rw [bulkTail,indicator_of_mem (show r∈Ioi (16:ℝ) from h),indicator_of_mem (show r∈Ioi (16:ℝ) from h)]
        conv_lhs => lhs; rw [←Real.rpow_one r]
        rw [←Real.rpow_add hr]; norm_num
      · simp [bulkTail,show r∉Ioi (16:ℝ) from h]
    rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num)),integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
    norm_num [Real.rpow_neg (by norm_num : (0:ℝ)≤16),←Real.sqrt_eq_rpow]
  exact ⟨Integrable.of_integral_ne_zero (hi ▸ (by norm_num)),hi⟩

private theorem stripWeight_integral :
    Integrable stripWeight upperArea ∧ (∫ z, stripWeight z ∂upperArea)=1 := by
  let f := poissonLine 0 1
  let g := (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ))
  have hf : Integrable f := Integrable.of_integral_ne_zero ((poissonLine_integral 0 zero_lt_one) ▸ pi_ne_zero)
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp))
  have hprod := hf.mul_prod hg
  have hp := Complex.volume_preserving_equiv_real_prod
  have hv : Integrable stripWeight volume := by
    have h := (hp.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding).mpr hprod
    unfold stripWeight
    simpa only [stripWeight,Function.comp_def,Complex.measurableEquivRealProd_apply,Measure.volume_eq_prod,f,g,mul_comm] using h
  have hi : Integrable stripWeight upperArea :=
    (hv.smul_measure (c:=ENNReal.ofReal (1/π)) ENNReal.ofReal_ne_top).restrict
  refine ⟨hi,?_⟩
  rw [upperArea_slices _ hi,smul_eq_mul]
  simp only [stripWeight,integral_const_mul,poissonLine_integral 0 zero_lt_one]
  rw [integral_mul_const,setIntegral_indicator measurableSet_Ioc,inter_eq_right.mpr Ioc_subset_Ioi_self]
  simp [pi_ne_zero]

private theorem unit_arg {z : ℂ} (hz : 0≤z.im) :
    (unitPolePick.value z).arg=π-(z+Complex.I).arg := by
  let w := z+Complex.I
  have hw : w∈upper := by change 0<z.im+1; linarith
  obtain ⟨hp,hπ⟩ := upper_arg_range hw
  have hn : w≠0 := fun h => by simpa [h,upper] using hw
  simp only [unitPolePick_value,pole,Complex.ofReal_one,sub_neg_eq_add]; change (-1/w).arg=π-w.arg
  have h := congrArg Real.Angle.toReal (Complex.arg_div_coe_angle (by norm_num : (-1:ℂ)≠0) hn)
  simpa only [Complex.arg_coe_angle_toReal_eq_arg,←Real.Angle.coe_sub,Complex.arg_neg_one,
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr (show π-w.arg∈Ioc (-π) π by constructor <;> linarith [pi_pos])] using h

private theorem correction_bulk {z : ℂ} (hz : 0≤z.im) (hr : 16<‖z+Complex.I‖) :
    ‖omegaCorrection z‖≤8/Real.sqrt ‖z+Complex.I‖ := by
  let r := ‖z+Complex.I‖
  have hr' : 16<r := hr
  have hrp : 0<r := by linarith
  have hs : 4≤ sqrt r := by rw [←Real.sqrt_sq (by norm_num : (0:ℝ)≤4)]; apply sqrt_le_sqrt; linarith
  have hi : z≠Complex.I := fun e => by rw [e,←two_mul,norm_mul,Complex.norm_I] at hr; norm_num at hr
  have hd : r/2≤‖z-Complex.I‖ := by
    have h := norm_add_le (z-Complex.I) (2*Complex.I)
    rw [show z-Complex.I+2*Complex.I=z+Complex.I by ring,norm_mul,Complex.norm_I] at h
    norm_num at h; change r≤_ at h; linarith
  have hlogw : ‖Complex.log (z+Complex.I)‖≤log r+π := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    rw [Complex.log_re,Complex.log_im,abs_of_nonneg (log_nonneg (by linarith : 1≤r))]
    exact add_le_add (le_refl _) (Complex.abs_arg_le_pi _)
  have hlogI : ‖Complex.log (Complex.I+Complex.I)‖≤3 := by
    have ha : (Complex.I+Complex.I).arg=π/2 := by rw [←two_mul,show (2:ℂ)=((2:ℝ):ℂ) by norm_num,Complex.arg_real_mul _ (by norm_num),Complex.arg_I]
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    rw [Complex.log_im,ha,Complex.log_re,←two_mul,norm_mul,Complex.norm_I]; norm_num
    rw [abs_of_nonneg (log_nonneg (by norm_num : (1:ℝ)≤2)),abs_of_nonneg (by positivity : 0≤π/2)]; linarith [pi_lt_d2,log_two_lt_d9]
  have hlog : log r≤2*sqrt r := by
    have h := log_le_rpow_div hrp.le (by norm_num : (0:ℝ)<1/2)
    rw [←Real.sqrt_eq_rpow] at h; linarith
  rw [omegaCorrection,dslope_of_ne _ hi,slope_def_field,norm_div]
  apply (div_le_div₀ (by positivity : 0≤4*sqrt r)
    ((norm_sub_le ..).trans (by linarith [pi_lt_d2])) (half_pos hrp) hd).trans
  rw [div_le_div_iff₀ (half_pos hrp) (sqrt_pos.mpr hrp)]
  nlinarith only [sq_sqrt hrp.le]

private def shiftedUnitDensity (w : ℂ) := witnessDensity unitPolePick.value singleWitness (w-Complex.I)

private def windowDensity (R : ℝ) (w : ℂ) :=
  if 1<w.im ∧ ‖w‖<R then shiftedUnitDensity w else 0

private def angularWindow (R r : ℝ) := if 16<r ∧ r<R then (r^2)⁻¹ else 0

private def truncationMajorant (w : ℂ) :=
  5*radialInvAnnulus 1 16 ‖w‖ +40*bulkTail ‖w‖+4*stripWeight w

private theorem majorant_integral :
    Integrable truncationMajorant upperArea ∧ (∫ w, truncationMajorant w ∂upperArea)≤39 := by
  obtain ⟨h₁,q₁⟩ := radialInvAnnulus_majorant (w:=0) (by simp) (a:=1) (b:=16) (by norm_num) (by norm_num)
  simp only [sub_zero,div_one] at h₁ q₁
  obtain ⟨h₂,q₂⟩ := bulkTail_integral
  obtain ⟨h₃,q₃⟩ := stripWeight_integral
  refine ⟨((h₁.const_mul 5).add (h₂.const_mul 40)).add (h₃.const_mul 4),?_⟩
  unfold truncationMajorant
  erw [integral_add ((h₁.const_mul 5).add (h₂.const_mul 40)) (h₃.const_mul 4),integral_add (h₁.const_mul 5) (h₂.const_mul 40)]
  simp only [integral_const_mul,q₂,q₃]
  have he : log 16=4*log 2 := by rw [show (16:ℝ)=2^4 by norm_num,log_pow]; norm_num
  linarith [he,log_two_lt_d9]

private theorem majorant_nonneg (w : ℂ) : 0≤truncationMajorant w := by
  have h₁ : 0≤radialInvAnnulus 1 16 ‖w‖ := indicator_nonneg (fun _ _ => by positivity) _
  have h₂ : 0≤bulkTail ‖w‖ := indicator_nonneg (fun r hr => Real.rpow_nonneg (show 0≤r by linarith [show 16<r from hr]) _) _
  have h₃ : 0≤ stripWeight w := by unfold stripWeight poissonLine; apply mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (by positivity)
  unfold truncationMajorant; positivity

private theorem window_error_bound (R : ℝ) {w : ℂ} (hw : w∈upper) :
    |windowDensity R w-angularWindow R ‖w‖*angularDeficit w.arg|≤truncationMajorant w := by
  let r := ‖w‖
  let θ := w.arg
  have ht := upper_arg_range hw
  have hθ : |π/2-θ|≤π/2 := abs_le.mpr ⟨by dsimp [θ]; linarith [ht.2],by dsimp [θ]; linarith [ht.1]⟩
  have hang : |angularDeficit θ|≤2 := by
    unfold angularDeficit k₀
    have hh := pow_le_pow_left₀ (abs_nonneg _) hθ 2
    rw [sq_abs] at hh
    have hπ := pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 2
    apply abs_le.mpr; constructor <;> nlinarith [sq_nonneg (π/2-θ)]
  have hstrip : 0≤ stripWeight w := by unfold stripWeight poissonLine; apply mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (by positivity)
  have h₁ : 0≤radialInvAnnulus 1 16 r := indicator_nonneg (fun _ _ => by positivity) _
  by_cases hR : r<R
  · by_cases hy : 1<w.im
    · let z := w-Complex.I
      have hz : 0≤z.im := by simp [z]; linarith
      have hwz : z+Complex.I=w := sub_add_cancel .. 
      have hr1 : 1<r := hy.trans_le (Complex.im_le_norm w)
      have hrp : 0<r := zero_lt_one.trans hr1
      have hs : ‖unitPolePick.value z‖=r⁻¹ := by simp [unitPolePick_value,pole,hwz,r]
      have hopt := unitPole_optimalWitness hz
      have hW := singlePole_witness_bounds 0 zero_lt_one zero_lt_one hz
      simp only [Complex.ofReal_zero,Complex.ofReal_one,one_mul,zero_sub,←unitPolePick_value,hopt] at hW
      have hden : shiftedUnitDensity w=r⁻¹^2*(k₀-‖((unitPolePick.value z).arg:ℂ)-singleWitness z‖^2) := by
        unfold shiftedUnitDensity witnessDensity; change ‖unitPolePick.value z‖^2*_=_; rw [hs]
      have hwd : windowDensity R w=shiftedUnitDensity w := if_pos ⟨hy,hR⟩
      rw [hwd,hden]
      by_cases ht : 16<r
      · have hangw : angularWindow R r=(r^2)⁻¹ := if_pos ⟨ht,hR⟩
        have harg := unit_arg hz
        rw [hwz] at harg
        have hrep : ((unitPolePick.value z).arg:ℂ)-singleWitness z = ((π/2-θ:ℝ):ℂ)-omegaCorrection z := by
          rw [harg,singleWitness]; dsimp [θ]; push_cast; ring
        let a : ℂ := ((π/2-θ:ℝ):ℂ)
        let b := omegaCorrection z
        have hna : ‖a‖≤π/2 := by dsimp only [a]; rwa [Complex.norm_real,Real.norm_eq_abs]
        have hnb : ‖b‖≤log 2 := omegaCorrection_bound hz
        have hsum : ‖a-b‖+‖a‖≤5 := by linarith [norm_sub_le a b,pi_lt_d2,log_two_lt_d9]
        have hdiff := abs_norm_sub_norm_le (a-b) a
        simp only [sub_sub_cancel_left,norm_neg] at hdiff
        have hsquare : |‖a-b‖^2-‖a‖^2|≤5*‖b‖ := by
          rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
          exact mul_le_mul hsum hdiff (abs_nonneg _) (by norm_num)
        have hbulk : ‖b‖≤8/sqrt r := by simpa only [b,r,hwz] using correction_bulk hz (by rwa [hwz])
        have hna2 : ‖a‖^2=(π/2-θ)^2 := by dsimp only [a]; rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
        change |r⁻¹^2*_ - angularWindow R r*angularDeficit θ|≤_
        rw [hangw,hrep,←inv_pow,angularDeficit,←hna2]
        have hf : |r⁻¹^2*(k₀-‖a-b‖^2)-r⁻¹^2*(k₀-‖a‖^2)|≤r⁻¹^2*(5*(8/sqrt r)) := by
          rw [←mul_sub,show (k₀-‖a-b‖^2)-(k₀-‖a‖^2)= -(‖a-b‖^2-‖a‖^2) by ring,
            abs_mul,abs_of_nonneg (sq_nonneg _),abs_neg]
          exact mul_le_mul_of_nonneg_left (hsquare.trans (mul_le_mul_of_nonneg_left hbulk (by norm_num))) (sq_nonneg _)
        apply hf.trans
        have htail : bulkTail r=r^(-(5/2:ℝ)) := indicator_of_mem (show r∈Ioi (16:ℝ) from ht) _
        have hpow : r^(-(5/2:ℝ))=(r^2*sqrt r)⁻¹ := by
          rw [Real.rpow_neg hrp.le,show (5/2:ℝ)=2+1/2 by norm_num,Real.rpow_add hrp,Real.rpow_two,←Real.sqrt_eq_rpow]
        change _≤5*radialInvAnnulus 1 16 r+40*bulkTail r+4*stripWeight w
        rw [htail,hpow]
        simp only [mul_inv_rev,div_eq_mul_inv,←inv_pow]
        linarith only [h₁,hstrip,show r⁻¹^2*(5*(8*(sqrt r)⁻¹))=40*((sqrt r)⁻¹*r⁻¹^2) by ring]
      · have hangw : angularWindow R r=0 := if_neg (fun h => ht h.1)
        change |r⁻¹^2*_-angularWindow R r*_|≤_
        rw [hangw,zero_mul,sub_zero,abs_mul,abs_of_nonneg (sq_nonneg _)]
        apply (mul_le_mul_of_nonneg_left (le_trans hW.2.2.2.le (by norm_num : (4.304:ℝ)≤5)) (sq_nonneg _)).trans
        change _≤5*radialInvAnnulus 1 16 r+40*bulkTail r+4*stripWeight w
        rw [radialInvAnnulus,indicator_of_mem (show r∈Ioc 1 16 from ⟨hr1,le_of_not_gt ht⟩),
          bulkTail,indicator_of_notMem (show r∉Ioi (16:ℝ) from ht),←inv_pow]
        linarith
    · rw [show windowDensity R w=0 from if_neg (fun h => hy h.1),zero_sub,abs_neg]
      by_cases ht : 16<r
      · have hangw : angularWindow R ‖w‖=(r^2)⁻¹ := if_pos ⟨ht,hR⟩
        rw [hangw,abs_mul,abs_of_nonneg (by positivity)]
        have hpo : (r^2)⁻¹ ≤ 2*poissonLine 0 1 w.re := by
          have hs : w.re^2≤r^2 := by dsimp [r]; rw [Complex.sq_norm,Complex.normSq_apply]; nlinarith [sq_nonneg w.im]
          have hr1 : 1≤r^2 := by nlinarith [show 0≤r from norm_nonneg _,ht]
          simp [poissonLine,←one_div]
          rw [←mul_div_assoc,mul_one]
          apply (div_le_div_iff₀ (by nlinarith [show 0≤r from norm_nonneg _,ht,hr1] : 0<r^2) (by positivity : 0<w.re^2+1)).mpr
          linarith
        have hst : stripWeight w=poissonLine 0 1 w.re := by
          unfold stripWeight; rw [indicator_of_mem (show w.im∈Ioc 0 1 from ⟨hw,le_of_not_gt hy⟩),one_mul]
        have H := mul_le_mul hpo hang (abs_nonneg _) (by unfold poissonLine; positivity)
        change _ ≤ 5*radialInvAnnulus 1 16 r+40*bulkTail r+4*stripWeight w
        rw [hst]; have ht' : 0≤bulkTail r := by rw [bulkTail,indicator_of_mem (show r∈Ioi (16:ℝ) from ht)]; positivity
        linarith
      · rw [show angularWindow R ‖w‖=0 from if_neg (fun h => ht h.1),zero_mul,abs_zero]; exact majorant_nonneg _
  · rw [show windowDensity R w=0 from if_neg (fun h => hR h.2),show angularWindow R ‖w‖=0 from if_neg (fun h => hR h.2)]
    simpa using majorant_nonneg w

private theorem measurable_singleWitness : Measurable singleWitness := by
  classical
  have he : omegaCorrection = fun z => if z=Complex.I then -Complex.I/2 else
      (Complex.log (z+Complex.I)-Complex.log (Complex.I+Complex.I))/(z-Complex.I) := by
    funext z; split_ifs with h
    · rw [h,omegaCorrection_at_I]
    · rw [omegaCorrection,dslope_of_ne _ h,slope_def_field]
  unfold singleWitness
  rw [he]
  apply measurable_const.add
  apply Measurable.ite (measurableSet_singleton Complex.I) measurable_const
  fun_prop

private theorem window_integral_bound (R : ℝ) : |∫ w, windowDensity R w ∂upperArea|≤39 := by
  let F := windowDensity R
  let G := fun w : ℂ => angularWindow R ‖w‖*angularDeficit w.arg
  have hF : Measurable F := by
    dsimp only [F,windowDensity]
    apply Measurable.ite ((measurableSet_lt measurable_const Complex.measurable_im).inter
      (measurableSet_lt measurable_norm measurable_const)) _ measurable_const
    unfold shiftedUnitDensity witnessDensity
    rw [unitPolePick_value]; unfold pole
    have hm := measurable_singleWitness.comp (measurable_id.sub_const Complex.I)
    fun_prop (disch := assumption)
  have hG : Measurable G := by
    dsimp only [G,angularWindow,angularDeficit]
    apply Measurable.mul
    · apply Measurable.ite ((measurableSet_lt measurable_const measurable_norm).inter
        (measurableSet_lt measurable_norm measurable_const)) (by fun_prop) measurable_const
    · fun_prop
  have hdiff : Integrable (fun w => F w-G w) upperArea := by
    apply majorant_integral.1.mono' (hF.sub hG).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
    exact window_error_bound R hw
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  letI : IsFiniteMeasureOnCompacts upperArea := by unfold upperArea; infer_instance
  have hball : upperArea (ball (0:ℂ) R) < ⊤ := measure_ball_lt_top
  have hI := (integrable_indicator_iff (μ:=upperArea) (isOpen_ball (x:=(0:ℂ)) (ε:=R)).measurableSet).mpr
    (integrableOn_const (C:=(40:ℝ)) hball.ne)
  have hiG : Integrable G upperArea := by
    apply hI.mono' hG.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
    by_cases h : 16<‖w‖ ∧ ‖w‖<R
    · have hmem : w∈ball (0:ℂ) R := by simpa using h.2
      change ‖angularWindow R ‖w‖*angularDeficit w.arg‖≤_
      rw [angularWindow,if_pos h,indicator_of_mem hmem,norm_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have ht := upper_arg_range hw
      have hx : |π/2-w.arg|≤π/2 := abs_le.mpr ⟨by linarith [ht.2],by linarith [ht.1]⟩
      have hs := pow_le_pow_left₀ (abs_nonneg _) hx 2
      rw [sq_abs] at hs
      have ha : ‖angularDeficit w.arg‖≤40 := by
        rw [Real.norm_eq_abs,angularDeficit,k₀,abs_le]
        constructor <;> nlinarith [pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 2,sq_nonneg (π/2-w.arg)]
      exact (mul_le_mul (inv_le_one_of_one_le₀ (by nlinarith [h.1] : 1≤‖w‖^2)) ha (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · simp only [G,angularWindow,if_neg h,zero_mul,norm_zero]
      exact indicator_nonneg (fun _ _ => by norm_num) _
  have hiF : Integrable F upperArea := by simpa only [Pi.add_def,sub_add_cancel] using hdiff.add hiG
  have h0 : (∫ w, G w ∂upperArea)=0 := upperArea_angular_cancel _
  have h := (norm_integral_le_of_norm_le majorant_integral.1 (f:=fun w => F w-G w)
    ((ae_restrict_iff' upper_open.measurableSet).mpr (ae_of_all _ (fun w hw => window_error_bound R hw)))).trans majorant_integral.2
  rwa [integral_sub hiF hiG,h0,sub_zero,Real.norm_eq_abs] at h

/-- The one-pole signed partial integral stays uniformly bounded at all cut
radii, even though its two unsigned terms grow logarithmically. -/
theorem unitPole_partial_density_bound (R : ℝ) :
    |∫ z in {z : ℂ | ‖z+Complex.I‖<R}, witnessDensity unitPolePick.value singleWitness z ∂upperArea|≤39 := by
  let D := {z : ℂ | 1<z.im ∧ ‖z‖<R}
  let T := {z : ℂ | ‖z+Complex.I‖<R}
  have hT : MeasurableSet T := measurableSet_lt (by fun_prop) measurable_const
  have hD : MeasurableSet D := (measurableSet_lt measurable_const Complex.measurable_im).inter (measurableSet_lt measurable_norm measurable_const)
  have hd : D ⊆ upper := fun w hw => lt_trans zero_lt_one hw.1
  have hp : MeasurePreserving (fun z : ℂ => z+Complex.I) area area := by
    have h := measurePreserving_add_right (volume:Measure ℂ) Complex.I
    exact ⟨h.measurable,by unfold area; rw [Measure.map_smul _ h.measurable.aemeasurable,h.map_eq]⟩
  have hpre : (fun z : ℂ => z+Complex.I) ⁻¹' D=T∩upper := by
    ext z; change (1<(z+Complex.I).im ∧ ‖z+Complex.I‖<R) ↔ _ ∧ 0<z.im
    simp only [Complex.add_im,Complex.I_im,lt_add_iff_pos_left]; tauto
  have he := hp.setIntegral_preimage_emb (Homeomorph.addRight Complex.I).measurableEmbedding shiftedUnitDensity D
  rw [hpre] at he
  simp only [shiftedUnitDensity,add_sub_cancel_right] at he
  have hwindow : windowDensity R = D.indicator shiftedUnitDensity := by
    funext w; by_cases hw : w∈D
    · rw [indicator_of_mem hw]; exact if_pos hw
    · rw [indicator_of_notMem hw]; exact if_neg hw
  have h := window_integral_bound R
  rw [hwindow,integral_indicator hD,upperArea,Measure.restrict_restrict hD,inter_eq_left.mpr hd] at h
  rw [upperArea,Measure.restrict_restrict hT,he]
  exact h

end Liu
