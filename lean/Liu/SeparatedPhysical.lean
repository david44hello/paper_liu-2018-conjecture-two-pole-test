import Liu.SeparatedFlux

noncomputable section
open Set Real MeasureTheory
open scoped ComplexConjugate
namespace Liu.PickChart

def realSum (P : PickChart) (r a : ℝ) (z : ℂ) : ℂ :=
  pole a (P.left r) z + pole (1-a) (P.right r) z

private theorem physical_factors {P : PickChart} {U : Set ℂ} (h : P.Regular U) {r a : ℝ}
    (hr : (r:ℂ)∈U) (ha : P.mass r=(a:ℂ)) {z : ℂ} (hz : 0≤z.im) :
    P.realSum r a z = P.value r z ∧
    deriv (P.realSum r a) z = P.valueFactor r z * P.derivativeRatio r z / (z+Complex.I)^2 := by
  have ne (p : ℂ) (hp : p.im < 0) : z ≠ p := fun e => by rw [e] at hz; linarith
  have hL := ne _ (h.left_below _ hr)
  have hR := ne _ (h.right_below _ hr)
  have hN := sub_ne_zero.mpr (ne _ (h.zero_below _ hr))
  have hZ : z+Complex.I ≠ 0 := by
    intro e
    have he := congrArg Complex.im e
    simp at he
    linarith
  have hf : z-P.zeroNode r = (a:ℂ)*(z-P.right r)+(1-(a:ℂ))*(z-P.left r) := by
    unfold zeroNode; rw [ha]; ring
  have hd := (pole_hasDerivAt (a:=a) hL).add (pole_hasDerivAt (a:=1-a) hR)
  constructor
  · unfold realSum value valueFactor nodeFactor pole
    rw [hf,Complex.ofReal_sub,Complex.ofReal_one]
    field_simp [sub_ne_zero.mpr hL,sub_ne_zero.mpr hR,hZ] <;> ring
  · change deriv (pole a (P.left r)+pole (1-a) (P.right r)) z=_
    rw [hd.deriv,derivativeRatio,valueFactor,ha,Complex.ofReal_sub,Complex.ofReal_one]
    simp only [nodeFactor]
    field_simp [sub_ne_zero.mpr hL,sub_ne_zero.mpr hR,hN,hZ] <;> ring

private theorem physical_source {P : PickChart} {U : Set ℂ} (h : P.Regular U) {r a : ℝ}
    (hr : (r:ℂ)∈U) (ha : P.mass r=(a:ℂ)) {z : ℂ} (hz : 0≤z.im) :
    source (P.realSum r a) z=(Complex.I/2)*P.rho r z := by
  have hL := (nodeFactor_bounds (h.left_below _ hr) hz).1
  have hR := (nodeFactor_bounds (h.right_below _ hr) hz).1
  have hN := (nodeFactor_bounds (h.zero_below _ hr) hz).1
  have hF : P.valueFactor r z ≠ 0 := mul_ne_zero (mul_ne_zero hN (inv_ne_zero hL)) (inv_ne_zero hR)
  have hZ : z+Complex.I ≠ 0 := by
    intro e; have he := congrArg Complex.im e; simp at he; linarith
  have hFb : conj (P.valueFactor r z) ≠ 0 := by simpa using hF
  have hZb : conj (z+Complex.I) ≠ 0 := (map_ne_zero_iff _ (starRingEnd ℂ).injective).mpr hZ
  obtain ⟨hV,hD⟩ := physical_factors h hr ha hz
  rw [source,hV,hD,value,rho,Complex.conj_ofReal,map_div₀,map_neg,map_div₀,map_pow,map_mul,
    Complex.ofReal_pow,←Complex.mul_conj']
  field_simp [hFb,hZb,hZ] <;> ring

/-- On the real slice the source integral is the actual physical boundary field. -/
theorem Regular.field_eq {P : PickChart} {U : Set ℂ} (h : P.Regular U) {r a : ℝ}
    (hr : (r:ℂ)∈U) (ha : P.mass r=(a:ℂ)) (h₀ : 0<a) (h₁ : a<1) (x : ℝ) :
    field (P.realSum r a) x = -P.trace r x := by
  let Q : Pair := ⟨a,1-a,P.left r,P.right r,h₀,by linarith,h.left_below _ hr,h.right_below _ hr⟩
  have hQ : Q.toPick.value=P.realSum r a := by
    funext z; simp [Q,Pair.toPick,PickSum.value,realSum,Fin.sum_univ_two]
  have ht := Q.toPick.field_on_boundary x
  rw [hQ] at ht
  rw [ht,poissonTrace,trace]
  let K := fun z : ℂ => ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*P.rho r z
  have he : (fun z : ℂ => ((2*z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*source (P.realSum r a) z) =ᵐ[upperArea]
      fun z => Complex.I*K z := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
    rw [physical_source h hr ha (le_of_lt hz)]
    dsimp [K]; push_cast; ring
  change Complex.I*(∫ z, _ ∂upperArea)= -(∫ z, K z ∂upperArea)
  rw [integral_congr_ae he,integral_const_mul,←mul_assoc,Complex.I_mul_I,neg_one_mul]

theorem Regular.flux_agrees {P : PickChart} {U : Set ℂ} (h : P.Regular U) {r a : ℝ}
    (hr : (r:ℂ)∈U) (ha : P.mass r=(a:ℂ)) (h₀ : 0<a) (h₁ : a<1) :
    P.fluxExtension r = (boundaryFlux (P.realSum r a):ℂ) := by
  have he (x : ℝ) : P.fluxIntegrand r x =
      ((‖field (P.realSum r a) x‖^2-k₀*‖P.realSum r a x‖^2:ℝ):ℂ) := by
    have hV := (physical_factors h hr ha (z:=(x:ℂ)) (by simp)).1
    unfold fluxIntegrand
    simp only [Complex.conj_ofReal,←hV]
    rw [mul_assoc (k₀:ℂ),Complex.mul_conj',Complex.mul_conj',h.field_eq hr ha h₀ h₁]
    simp
  unfold fluxExtension boundaryFlux
  simp_rw [he,integral_complex_ofReal,Complex.ofReal_div]

end Liu.PickChart
