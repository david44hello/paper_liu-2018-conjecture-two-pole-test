module

public import Liu.WitnessClaim
public import Liu.SinglePoleEvaluation
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped Topology ComplexConjugate Interval
namespace Liu

def omegaCorrection := dslope (fun z : ℂ => Complex.log (z+Complex.I)) Complex.I
def singleWitness (z : ℂ) := ((π/2:ℝ):ℂ)+omegaCorrection z

theorem omegaCorrection_regular :
    DifferentiableOn ℂ omegaCorrection {z : ℂ | -1<z.im} := by
  let U := {z : ℂ | -1<z.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hI : Complex.I∈U := by change -1<Complex.I.im; norm_num
  apply (Complex.differentiableOn_dslope (hU.mem_nhds hI)).mpr
  intro z hz
  have hip : 0<(z+Complex.I).im := by simp; linarith [show -1<z.im from hz]
  exact (((hasDerivAt_id z).add_const Complex.I).clog (Complex.mem_slitPlane_iff.mpr (Or.inr hip.ne'))).differentiableAt.differentiableWithinAt

theorem omegaCorrection_at_I : omegaCorrection Complex.I= -Complex.I/2 := by
  rw [omegaCorrection,dslope_same]
  have h := ((hasDerivAt_id Complex.I).add_const Complex.I).clog
    (show Complex.I+Complex.I∈Complex.slitPlane by apply Complex.mem_slitPlane_iff.mpr; right; simp)
  simp only [id_eq] at h
  rw [h.deriv]; field_simp [Complex.I_ne_zero] <;> ring_nf <;> simp [Complex.I_sq]

theorem omegaCorrection_integral {z : ℂ} (hz : 0≤z.im) :
    omegaCorrection z = ∫ t in (0:ℝ)..1, (2*Complex.I+(t:ℂ)*(z-Complex.I))⁻¹ := by
  by_cases hn : z=Complex.I
  · subst z; rw [omegaCorrection_at_I]; simp [Complex.I_mul_I,mul_inv_rev,div_eq_mul_inv,mul_comm]
  let g := fun t : ℝ => 2*Complex.I+(t:ℂ)*(z-Complex.I)
  have hp (t : ℝ) (ht : t∈uIcc (0:ℝ) 1) : 0<(g t).im := by
    rw [uIcc_of_le zero_le_one] at ht
    dsimp [g]; simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.im_ofNat,Complex.re_ofNat,Complex.I_re,Complex.I_im,Complex.sub_im,zero_mul,mul_one,add_zero]
    nlinarith [mul_nonneg ht.1 hz,ht.2]
  have hs (t : ℝ) (ht : t∈uIcc (0:ℝ) 1) : g t∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr (hp t ht).ne')
  have dg (t : ℝ) (ht : t∈uIcc (0:ℝ) 1) : HasDerivAt (fun u => Complex.log (g u)) ((z-Complex.I)*(g t)⁻¹) t := by
    have h := (((hasDerivAt_id (t:ℂ)).mul_const (z-Complex.I)).const_add (2*Complex.I)).clog (hs t ht)
    simpa [g,div_eq_mul_inv] using h.comp_ofReal
  have hg : ContinuousOn (fun t => (z-Complex.I)*(g t)⁻¹) (uIcc 0 1) := by
    intro t ht; have hne : g t≠0 := fun he => by have := hp t ht; simp [he] at this
    dsimp [g] at hne ⊢; fun_prop (disch := assumption)
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt dg hg.intervalIntegrable
  rw [intervalIntegral.integral_const_mul] at hft
  rw [omegaCorrection,dslope_of_ne _ hn,slope_def_field]
  rw [show g 1=z+Complex.I by dsimp [g]; simp; ring,show g 0=Complex.I+Complex.I by dsimp [g]; simp; ring] at hft
  change (Complex.log (z+Complex.I)-Complex.log (Complex.I+Complex.I))/(z-Complex.I)=∫ t in (0:ℝ)..1, (g t)⁻¹
  exact (div_eq_iff (sub_ne_zero.mpr hn)).mpr (hft.symm.trans (mul_comm ..))

theorem omegaCorrection_bound {z : ℂ} (hz : 0≤z.im) : ‖omegaCorrection z‖≤log 2 := by
  rw [omegaCorrection_integral hz,intervalIntegral.integral_of_le zero_le_one]
  have hpos (t : ℝ) (ht : t∈Ioc (0:ℝ) 1) : 0<2-t := by linarith [ht.2]
  have hc : ContinuousOn (fun t : ℝ => (2-t)⁻¹) (Icc 0 1) := by
    intro t ht; fun_prop (disch := first | linarith [ht.2])
  have hi : IntegrableOn (fun t : ℝ => (2-t)⁻¹) (Ioc 0 1) volume := hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply (norm_integral_le_of_norm_le hi ?_).trans_eq
  · rw [←intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹),
      show (2:ℝ)-1=1 by norm_num,sub_zero,integral_inv_of_pos (by norm_num) (by norm_num),div_one]
  · filter_upwards [ae_restrict_mem (μ:=(volume:Measure ℝ)) measurableSet_Ioc] with t ht
    let w := 2*Complex.I+(t:ℂ)*(z-Complex.I)
    have him : 2-t≤w.im := by dsimp [w]; simp [Complex.mul_im,Complex.mul_re]; nlinarith [mul_nonneg ht.1.le hz]
    rw [norm_inv]; exact inv_anti₀ (hpos t ht) (him.trans (Complex.im_le_norm _))

theorem omegaCorrection_at_zero : omegaCorrection 0= -Complex.I*(log 2:ℝ) := by
  rw [omegaCorrection,dslope_of_ne _ Complex.I_ne_zero.symm,slope_def_field]
  simp only [zero_add,zero_sub,←two_mul,Complex.log_I]
  have he : Complex.log (2*Complex.I)=(log 2:ℝ)+(π/2:ℝ)*Complex.I := by
    have ha : (2*Complex.I).arg=π/2 := by rw [show (2:ℂ)*Complex.I=((2:ℝ):ℂ)*Complex.I by norm_num,Complex.arg_real_mul _ (by norm_num),Complex.arg_I]
    apply Complex.ext <;> simp [Complex.log_re,Complex.log_im,ha]
  rw [he]; push_cast; field_simp [Complex.I_ne_zero]; ring_nf <;> simp [Complex.I_sq]

theorem singleWitness_isWitness : isWitness singleWitness := by
  have hu : upper ⊆ {z : ℂ | -1<z.im} := fun z hz => by change -1<z.im; linarith [show 0<z.im from hz]
  have hv : {z : ℂ | 0≤z.im} ⊆ {z : ℂ | -1<z.im} := fun z hz => by change -1<z.im; linarith [show 0≤z.im from hz]
  refine ⟨(omegaCorrection_regular.mono hu).const_add _,
    continuousOn_const.add (omegaCorrection_regular.continuousOn.mono hv),?_⟩
  let K := 2*(1+log 2+π+‖Complex.log (2*Complex.I)‖)
  have hl := log_nonneg (by norm_num : (1:ℝ)≤2)
  refine ⟨K,by dsimp [K]; positivity,2,by norm_num,?_⟩
  intro z hz hr
  let r := ‖z‖
  have h1 : 1≤r := by dsimp [r]; linarith
  have hrp := zero_lt_one.trans_le h1
  have hn : z≠Complex.I := fun he => by rw [he,Complex.norm_I] at hr; linarith
  have hplus := norm_add_le z Complex.I
  rw [Complex.norm_I] at hplus
  have hnorm : 1≤‖z+Complex.I‖ := by
    apply le_trans _ (Complex.im_le_norm _); simp; exact hz
  have hlog : ‖Complex.log (z+Complex.I)‖≤log r+log 2+π := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    rw [Complex.log_re,abs_of_nonneg (log_nonneg hnorm),Complex.log_im]
    apply add_le_add _ (Complex.abs_arg_le_pi _)
    rw [←log_mul hrp.ne' (by norm_num)]
    exact log_le_log (zero_lt_one.trans_le hnorm) (by dsimp only [r] at *; linarith)
  have hsep : r/2≤‖z-Complex.I‖ := by
    have h := norm_sub_le_norm_sub_add_norm_sub z Complex.I 0
    simp only [sub_zero,Complex.norm_I] at h
    dsimp only [r] at *; linarith
  rw [singleWitness,add_sub_cancel_left,omegaCorrection,dslope_of_ne _ hn,slope_def_field,norm_div,←two_mul]
  apply (div_le_div₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_sub_le ..) (half_pos hrp) hsep).trans
  change _≤K*(1+log r)/r
  have h := add_le_add hlog (le_refl ‖Complex.log (2*Complex.I)‖)
  apply (div_le_div_of_nonneg_right h (half_pos hrp).le).trans
  apply (div_le_div_iff₀ (half_pos hrp) hrp).mpr
  dsimp only [K]
  nlinarith only [mul_nonneg (mul_nonneg (add_nonneg (add_nonneg hl pi_pos.le) (norm_nonneg (Complex.log (2*Complex.I)))) (log_nonneg h1)) hrp.le,hrp.le]

theorem omegaCorrection_sup : sSup (Set.range (fun z : {w : ℂ // 0≤w.im} => ‖omegaCorrection z‖))=log 2 := by
  have h0 : ‖omegaCorrection 0‖=log 2 := by rw [omegaCorrection_at_zero,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg (log_nonneg (by norm_num))]
  letI : Nonempty {z : ℂ // 0≤z.im} := ⟨⟨0,by simp⟩⟩
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _); rintro y ⟨z,rfl⟩; exact omegaCorrection_bound z.property
  · apply le_csSup (show BddAbove (Set.range (fun z : {w : ℂ // 0≤w.im} => ‖omegaCorrection z‖)) from
      ⟨log 2,fun y ⟨z,hz⟩ => hz ▸ omegaCorrection_bound z.property⟩)
    exact ⟨⟨0,by simp⟩,h0⟩

end Liu
