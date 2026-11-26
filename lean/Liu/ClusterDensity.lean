import Liu.ClusterGeometry

noncomputable section
open Set Real MeasureTheory Metric
open scoped Topology ComplexConjugate
namespace Liu

def witnessDensity (S W : ℂ → ℂ) (z : ℂ) : ℝ :=
  ‖S z‖^2*(k₀-‖((S z).arg:ℂ)-W z‖^2)

private theorem squared_norm_difference (a b : ℂ) :
    |‖a‖^2-‖b‖^2| ≤ ‖a-b‖*(‖a‖+‖b‖) := by
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [mul_comm (‖a‖+‖b‖)]
  exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le ..) (by positivity)

private theorem perturbed_witness_density {A B W η : ℂ} (hA : A∈upper) (hB : B∈upper)
    (he : A=B*(1+η)) (hη : ‖η‖≤1/8)
    (hw : ‖(B.arg:ℂ)-W‖<2.264) (hk : |k₀-‖(B.arg:ℂ)-W‖^2|<4.304) :
    |‖A‖^2*(k₀-‖(A.arg:ℂ)-W‖^2)-‖B‖^2*(k₀-‖(B.arg:ℂ)-W‖^2)| ≤ 30*‖B‖^2*‖η‖ := by
  obtain ⟨ha,hπa⟩ := upper_arg_range hA
  obtain ⟨hb,hπb⟩ := upper_arg_range hB
  have hBn : B≠0 := fun h => by simpa [h,upper] using hB
  have hAn : A≠0 := fun h => by simpa [h,upper] using hA
  have hd : (1+η).arg=A.arg-B.arg := by
    have h := congrArg Real.Angle.toReal (Complex.arg_div_coe_angle hAn hBn)
    rw [show A/B=1+η by rw [he]; field_simp] at h
    simpa only [Complex.arg_coe_angle_toReal_eq_arg,←Real.Angle.coe_sub,
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr (show A.arg-B.arg∈Ioc (-π) π by constructor <;> linarith)] using h
  have harg := arg_one_add_bound (show ‖η‖≤1 by linarith)
  rw [hd] at harg
  let U := (A.arg:ℂ)-W
  let V := (B.arg:ℂ)-W
  have hdiff : ‖U-V‖≤2*‖η‖ := by
    have h : U-V=((A.arg-B.arg:ℝ):ℂ) := by dsimp [U,V]; push_cast; ring
    rw [h,Complex.norm_real,Real.norm_eq_abs]
    exact harg.trans (mul_le_mul_of_nonneg_right (by linarith [pi_lt_d2]) (norm_nonneg _))
  have hU := norm_sub_le_norm_sub_add_norm_sub U V 0
  simp only [sub_zero] at hU
  have hV : ‖V‖<2.264 := hw
  have hab : |‖U‖^2-‖V‖^2| ≤ 10*‖η‖ := by
    apply (squared_norm_difference ..).trans
    have hsum : ‖U‖+‖V‖≤5 := by linarith
    exact (mul_le_mul hdiff hsum (by positivity) (by positivity)).trans_eq (by ring)
  have ht : ‖1+η‖≤1+‖η‖ := by simpa using norm_add_le (1:ℂ) η
  have ht2 : ‖1+η‖^2≤1.5 := by nlinarith only [pow_le_pow_left₀ (norm_nonneg (1+η)) (ht.trans (show 1+‖η‖≤1+1/8 by linarith)) 2]
  have ht' : |‖1+η‖^2-1|≤3*‖η‖ := by
    have h := squared_norm_difference (1+η) 1
    simp only [norm_one,one_pow,add_sub_cancel_left] at h
    exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_left (show ‖1+η‖+1≤3 by linarith) (norm_nonneg η)])
  have he' : ‖A‖=‖B‖*‖1+η‖ := by rw [he,norm_mul]
  change |‖A‖^2*(k₀-‖U‖^2)-‖B‖^2*(k₀-‖V‖^2)|≤_
  rw [he',show (‖B‖*‖1+η‖)^2*(k₀-‖U‖^2)-‖B‖^2*(k₀-‖V‖^2)=
      ‖B‖^2*((‖1+η‖^2-1)*(k₀-‖V‖^2)-‖1+η‖^2*(‖U‖^2-‖V‖^2)) by ring,
    abs_mul,abs_of_nonneg (sq_nonneg _)]
  rw [mul_comm 30,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (abs_sub ..).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg ‖1+η‖)]
  have h₁ := mul_le_mul ht' (show |k₀-‖V‖^2|≤5 by linarith [show |k₀-‖V‖^2|<4.304 from hk]) (abs_nonneg _) (by positivity)
  have h₂ := mul_le_mul ht2 hab (abs_nonneg _) (by norm_num)
  linarith [norm_nonneg η]

/-- The exact integral of the fourth-power pole majorant is the diagonal value
of the half-plane Bergman kernel. -/
theorem fourth_pole_integral {w : ℂ} (hw : w.im<0) :
    Integrable (fun z : ℂ => (‖z-w‖^4)⁻¹) upperArea ∧
    (∫ z : ℂ, (‖z-w‖^4)⁻¹ ∂upperArea) = 1/(4*w.im^2) := by
  let c := conj w
  have hc : c∈upper := by simpa [upper,c] using neg_pos.mpr hw
  have hp := bergmanKernel_memLp hc
  have hi := (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp
  have he (z : ℂ) : ‖bergmanKernel c z‖^2=(‖z-w‖^4)⁻¹ := by
    simp [bergmanKernel,c,norm_pow,←inv_pow,←pow_mul]
  refine ⟨by simpa only [he] using hi,?_⟩
  have h := bergman_reproducing hp (bergmanKernel_analytic hc) hc
  simp only [Complex.mul_conj',←Complex.ofReal_pow,integral_complex_ofReal,he] at h
  have hsub : c-conj c= - (2*w.im:ℝ)*Complex.I := by dsimp [c]; apply Complex.ext <;> simp <;> ring
  have hkernel : bergmanKernel c c=((1/(4*w.im^2):ℝ):ℂ) := by
    rw [bergmanKernel,hsub]; push_cast; rw [mul_pow,Complex.I_sq]; ring
  rw [hkernel] at h
  exact Complex.ofReal_inj.mp h

def Pair.centrePick (p : Pair) := singlePick p.mass p.massCentre.re (-p.massCentre.im)
  p.mass_pos (neg_pos.mpr p.massCentre_below)

private theorem centre_coordinates (p : Pair) :
    (p.massCentre.re:ℂ)-((-p.massCentre.im:ℝ):ℂ)*Complex.I=p.massCentre := by
  apply Complex.ext <;> simp

theorem Pair.centrePick_value (p : Pair) : p.centrePick.value=pole p.mass p.massCentre := by
  rw [Pair.centrePick,singlePick_value,centre_coordinates]

theorem Pair.cluster_density_bound (p : Pair) (hd : p.separation≤ -p.massCentre.im/4)
    {z : ℂ} (hz : 0≤z.im) :
    let S := p.centrePick.value
    let W := optimalWitness S
    |witnessDensity p.value W z-witnessDensity S W z| ≤
      (60*p.a₁*p.a₂*p.separation^2)*(‖z-p.massCentre‖^4)⁻¹ := by
  let μ := p.massFraction
  let r := ‖z-p.massCentre‖
  have hr : 0<r := (neg_pos.mpr p.massCentre_below).trans_le ((show -p.massCentre.im≤(z-p.massCentre).im by
    rw [Complex.sub_im]; linarith).trans (Complex.im_le_norm _))
  have hc := singlePole_witness_bounds p.massCentre.re p.mass_pos (neg_pos.mpr p.massCentre_below) hz
  dsimp only at hc
  rw [centre_coordinates,←p.centrePick_value] at hc
  have he := p.value_cluster_factor hz
  rw [←p.centrePick_value] at he
  obtain ⟨hη,hsmall⟩ := p.clusterError_bound hd hz
  have h := perturbed_witness_density (W:=optimalWitness p.centrePick.value z) (p.im_pos hz) (p.centrePick.value_im_pos hz)
    he hsmall (hc.1.trans_lt hc.2.1) hc.2.2.2
  change |witnessDensity p.value _ z-witnessDensity p.centrePick.value _ z|≤_
  apply h.trans
  apply (mul_le_mul_of_nonneg_left hη (by positivity : 0≤30*‖p.centrePick.value z‖^2)).trans_eq
  have hm : p.mass^2*(μ*(1-μ))=p.a₁*p.a₂ := by
    dsimp only [μ,Pair.massFraction]
    field_simp [p.mass_pos.ne']; dsimp [Pair.mass]; ring
  rw [p.centrePick_value]
  simp only [pole,norm_div,norm_neg,Complex.norm_of_nonneg p.mass_pos.le]
  change 30*(p.mass/r)^2*(2*(μ*(1-μ))*p.separation^2/r^2)=_
  rw [show 60*p.a₁*p.a₂=60*(p.a₁*p.a₂) by ring,←hm]
  change _ = 60*(p.mass^2*(μ*(1-μ)))*p.separation^2*(r^4)⁻¹
  ring

end Liu
