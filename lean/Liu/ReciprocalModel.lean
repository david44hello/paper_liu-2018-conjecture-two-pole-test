import Liu.ParameterDiscIntegral
import Liu.CertificateConclusion
import Liu.Dilation

noncomputable section
open Set Real MeasureTheory Metric
open scoped ComplexConjugate Topology
namespace Liu

def unitDepthSum (s γ v : ℝ) (z : ℂ) : ℂ :=
  pole (normalMass s) (-Complex.I) z +
  pole (1-normalMass s) (-Complex.I+(v:ℂ)*direction γ) z

def unitDepthPair (s γ v : ℝ) (hg : γ∈Icc 0 π) (hv : 0≤v) : Pair where
  a₁ := normalMass s
  a₂ := 1-normalMass s
  w₁ := -Complex.I
  w₂ := -Complex.I+(v:ℂ)*direction γ
  ha₁ := Certificate.normalMass_pos s
  ha₂ := Certificate.complement_normalMass s ▸ Certificate.normalMass_pos (-s)
  hw₁ := by simp
  hw₂ := by
    have hs := sin_nonneg_of_nonneg_of_le_pi hg.1 hg.2
    simp [Complex.add_im,Complex.mul_im,direction_im]; nlinarith [mul_nonneg hv hs]

theorem unitDepthPair_value (s γ v : ℝ) (hg : γ∈Icc 0 π) (hv : 0≤v) :
    (unitDepthPair s γ v hg hv).toPick.value=unitDepthSum s γ v := by
  funext z; simp [unitDepthPair,Pair.toPick,PickSum.value,unitDepthSum,Fin.sum_univ_two]

theorem boundaryFlux_dilation (S : ℂ → ℂ) {d : ℝ} (hd : 0<d) :
    boundaryFlux (dilateFunction S d)=d*boundaryFlux S := by
  let f := fun x : ℝ => ‖field S x‖^2-k₀*‖S x‖^2
  have he (x : ℝ) : ‖field (dilateFunction S d) x‖^2-k₀*‖dilateFunction S d x‖^2=d^2*f (d*x) := by
    simp only [field_dilate S hd,dilateFunction,f,Complex.real_smul,Complex.ofReal_mul,norm_mul,
      Complex.norm_of_nonneg hd.le,mul_pow]
    ring
  unfold boundaryFlux
  simp_rw [he,integral_const_mul,Measure.integral_comp_mul_left,smul_eq_mul,abs_of_pos (inv_pos.mpr hd)]
  change d^2*(d⁻¹*∫ x, f x)/π=d*((∫ x, f x)/π)
  field_simp [hd.ne',pi_ne_zero] <;> ring

/-- Reciprocal-depth homogeneity before removing the coalescing-pole zero. -/
theorem reciprocal_flux_scaling (s γ : ℝ) {u : ℝ} (hu : 0<u) :
    u^2*flux s γ u = (1/u)⁻¹*boundaryFlux (unitDepthSum s γ (1/u)) := by
  have scale (a : ℝ) (w z : ℂ) : pole a (w/(u:ℂ)) z = (u:ℂ)*pole a w ((u:ℂ)*z) := by
    rw [pole,pole,show z-w/(u:ℂ)=((u:ℂ)*z-w)/(u:ℂ) by field_simp [Complex.ofReal_ne_zero.mpr hu.ne']]
    rw [div_div_eq_mul_div]; ring
  have he : unitDepthSum s γ (1/u)=dilateFunction (normalSum s γ u) u := by
    funext z
    have h₁ : -(u:ℂ)*Complex.I/(u:ℂ)= -Complex.I := by field_simp [Complex.ofReal_ne_zero.mpr hu.ne']
    have h₂ : (-(u:ℂ)*Complex.I+direction γ)/(u:ℂ)= -Complex.I+((1/u:ℝ):ℂ)*direction γ := by
      push_cast; field_simp [Complex.ofReal_ne_zero.mpr hu.ne'] <;> ring
    simp only [unitDepthSum,dilateFunction,normalSum,Complex.real_smul]
    rw [←h₂,←h₁,scale,scale,mul_add]
  rw [he,boundaryFlux_dilation _ hu]
  change u^2*flux s γ u=(1/u)⁻¹*(u*flux s γ u)
  simp [one_div,pow_two,mul_assoc]

theorem unitDepth_flux_zero (s γ : ℝ) : boundaryFlux (unitDepthSum s γ 0)=0 := by
  have h : unitDepthSum s γ 0=pole 1 (-Complex.I) := by
    funext z; simp [unitDepthSum,pole,div_eq_mul_inv]; ring
  rw [h]
  simpa only [boundaryFlux,Complex.ofReal_zero,Complex.ofReal_one,one_mul,zero_sub] using
    single_pole_flux_zero 0 (m:=1) (b:=1) zero_lt_one zero_lt_one

/-- Dimensionless numerator factors in the half-plane source and its
conjugate partner. Both arguments are linear in the complex separation. -/
def topFactor (a : ℝ) (t : ℂ) : ℂ := (1-(a:ℂ)*t)/(1-t)
def topDerivFactor (a : ℝ) (t : ℂ) : ℂ := (a:ℂ)+(1-a)/(1-t)^2
def topValue (a : ℝ) (q w Z : ℂ) : ℂ := -topFactor a (w*q/Z)/Z
def topRho (a : ℝ) (q w Z : ℂ) : ℂ :=
  topFactor a (w*q/Z)/topFactor a (w*conj q/conj Z)*topDerivFactor a (w*conj q/conj Z) /
    ((‖Z‖^2:ℝ):ℂ)

theorem top_arg_bound {q w Z : ℂ} (hq : ‖q‖=1) (hZ : 1≤‖Z‖) :
    ‖w*q/Z‖≤‖w‖ := by
  rw [norm_div,norm_mul,hq,mul_one,div_le_iff₀ (by linarith)]
  exact le_mul_of_one_le_right (norm_nonneg _) hZ

private theorem sub_unit_comparison {t : ℂ} {r : ℝ} (ht : ‖t‖≤r) :
    1-r≤‖1-t‖ ∧ ‖1-t‖≤1+r := by
  have h := norm_sub_le_norm_sub_add_norm_sub (1:ℂ) t 0
  simp only [sub_zero,norm_one] at h
  exact ⟨by linarith,(norm_sub_le ..).trans (by simpa using add_le_add_left ht 1)⟩

theorem top_factors {a r : ℝ} (ha : 0≤a) (ha₁ : a≤1) (hr : r<1) {t : ℂ} (ht : ‖t‖≤r) :
    let K := (1+r)/(1-r)
    (1-t≠0 ∧ topFactor a t≠0) ∧ ‖topFactor a t‖≤K ∧ ‖(topFactor a t)⁻¹‖≤K ∧
      ‖topDerivFactor a t‖≤1+1/(1-r)^2 := by
  have hat : ‖(a:ℂ)*t‖≤r := by
    rw [norm_mul,Complex.norm_of_nonneg ha]
    exact (mul_le_of_le_one_left (norm_nonneg _) ha₁).trans ht
  have hA := sub_unit_comparison hat
  have hB := sub_unit_comparison ht
  have hp : 0<1-r := by linarith
  have hn : 0≤1+r := by linarith [norm_nonneg t]
  have hzA := norm_pos_iff.mp (hp.trans_le hA.1)
  have hzB := norm_pos_iff.mp (hp.trans_le hB.1)
  refine ⟨⟨hzB,div_ne_zero hzA hzB⟩,?_,?_,?_⟩
  · rw [topFactor,norm_div]; exact div_le_div₀ hn hA.2 hp hB.1
  · rw [topFactor,inv_div,norm_div]; exact div_le_div₀ hn hB.2 hp hA.1
  · unfold topDerivFactor
    apply (norm_add_le ..).trans
    rw [Complex.norm_of_nonneg ha,norm_div,norm_pow,show (1:ℂ)-(a:ℂ)=((1-a:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_of_nonneg (sub_nonneg.mpr ha₁)]
    exact add_le_add ha₁ (div_le_div₀ zero_le_one (by linarith) (sq_pos_of_pos hp) (pow_le_pow_left₀ hp.le hB.1 2))

theorem top_rational_bounds {a r : ℝ} (ha : 0≤a) (ha₁ : a≤1) (hr : r<1)
    {q w Z : ℂ} (hq : ‖q‖=1) (hZ : 1≤‖Z‖) (hw : ‖w‖≤r) :
    let K := (1+r)/(1-r)
    ‖topValue a q w Z‖≤K/‖Z‖ ∧
    ‖topRho a q w Z‖≤(K*K*(1+1/(1-r)^2))/‖Z‖^2 := by
  have hu := top_factors ha ha₁ hr ((top_arg_bound hq hZ).trans hw)
  have hv := top_factors ha ha₁ hr ((top_arg_bound (q:=conj q) (Z:=conj Z) (by simpa using hq) (by simpa using hZ)).trans hw)
  have hK : 0≤(1+r)/(1-r) := (norm_nonneg _).trans hu.2.1
  constructor
  · simpa [topValue,norm_div] using div_le_div_of_nonneg_right hu.2.1 (norm_nonneg Z)
  · simp only [topRho,norm_div,norm_mul,Complex.norm_of_nonneg (sq_nonneg _)]
    rw [div_eq_mul_inv ‖topFactor a (w*q/Z)‖,←norm_inv]
    apply div_le_div_of_nonneg_right _ (sq_nonneg ‖Z‖)
    exact mul_le_mul (mul_le_mul hu.2.1 hv.2.2.1 (norm_nonneg _) hK) hv.2.2.2 (norm_nonneg _) (mul_nonneg hK hK)

end Liu
