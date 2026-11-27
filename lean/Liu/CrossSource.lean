module

public import Liu.Geometry

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace Liu

def edgeSum (a : ℝ) (q z : ℂ) : ℂ :=
  -(a:ℂ)/z - (1-(a:ℂ))/(z-q)

def crossSource (a : ℝ) (q z : ℂ) : ℂ :=
  edgeSum a q z / conj (edgeSum a q z) * conj (deriv (edgeSum a q) z)
  - (a/‖z‖^2:ℝ) - ((1-a)/‖z-q‖^2:ℝ)

theorem edgeSum_eq {a : ℝ} {q z : ℂ} (hz : z ≠ 0) (hd : z-q ≠ 0) :
    edgeSum a q z = -(z-(a:ℂ)*q)/(z*(z-q)) := by
  unfold edgeSum
  field_simp
  ring

theorem edgeSum_deriv {a : ℝ} {q z : ℂ} (hz : z ≠ 0) (hd : z-q ≠ 0) :
    deriv (edgeSum a q) z = (a:ℂ)/z^2 + (1-(a:ℂ))/(z-q)^2 := by
  have d₁ := (hasDerivAt_const z (-(a:ℂ))).div (hasDerivAt_id z) hz
  have d₂ := (hasDerivAt_const z (1-(a:ℂ))).div ((hasDerivAt_id z).sub_const q) hd
  exact (d₁.sub d₂).deriv.trans (by simp; ring)

private theorem coe_sq_norm (z : ℂ) : ((‖z‖^2 : ℝ):ℂ) = z*conj z := by
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]

private theorem factored_source {a : ℝ} {q z : ℂ}
    (hz : z ≠ 0) (hd : z-q ≠ 0) (hc : z-(a:ℂ)*q ≠ 0) :
    crossSource a q z = (a:ℂ)*(1-a)*conj q/(conj z-(a:ℂ)*conj q) *
      (1/(z*(conj z-conj q))-1/((z-q)*conj z)) := by
  have hbz : conj z ≠ 0 := by simpa
  have hbd : conj z - conj q ≠ 0 := by simpa only [←map_sub,map_ne_zero] using hd
  have hbc : conj z - (a:ℂ)*conj q ≠ 0 := by
    simpa using (map_ne_zero (f := conj) (a := z-(a:ℂ)*q)).mpr hc
  unfold crossSource
  rw [edgeSum_deriv hz hd,edgeSum_eq hz hd]
  simp only [map_div₀,map_neg,map_sub,map_mul,map_add,map_pow,map_one,Complex.conj_ofReal,
    Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_one,coe_sq_norm]
  field_simp
  ring

theorem crossSource_formula {a : ℝ} {q z : ℂ}
    (hz : z ≠ 0) (hd : z-q ≠ 0) (hc : z-(a:ℂ)*q ≠ 0) :
    crossSource a q z =
      (2*Complex.I*(a:ℂ)*(1-a)*conj q*(z*conj q).im) /
        (((‖z‖^2*‖z-q‖^2:ℝ):ℂ)*(conj z-(a:ℂ)*conj q)) := by
  have hbz : conj z ≠ 0 := by simpa
  have hbd : conj z - conj q ≠ 0 := by simpa only [←map_sub,map_ne_zero] using hd
  have hbc : conj z - (a:ℂ)*conj q ≠ 0 := by
    simpa using (map_ne_zero (f := conj) (a := z-(a:ℂ)*q)).mpr hc
  have imid := Complex.sub_conj (z*conj q)
  simp only [map_mul,Complex.conj_conj,Complex.ofReal_mul,Complex.ofReal_ofNat] at imid
  rw [factored_source hz hd hc,Complex.ofReal_mul,coe_sq_norm,coe_sq_norm,map_sub]
  field_simp
  rw [mul_comm z (conj q)] at imid
  linear_combination (a:ℂ)*(1-a)*conj q * imid

theorem crossSource_real {a : ℝ} {q z : ℂ} (hq : ‖q‖ = 1)
    (hz : z ≠ 0) (hd : z-q ≠ 0) (hc : z-(a:ℂ)*q ≠ 0) :
    (crossSource a q z).re = -2*a*(1-a)*(z*conj q).im^2 /
      (‖z‖^2*‖z-q‖^2*‖z-(a:ℂ)*q‖^2) := by
  let c := z-(a:ℂ)*q
  let Y := (z*conj q).im
  let R := ‖z‖^2*‖z-q‖^2
  have hq' : q * conj q = 1 := by rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hq]; norm_num
  have hc' : c ≠ 0 := hc
  have hbc : conj c ≠ 0 := by simpa
  have hR : R ≠ 0 := by dsimp [R]; positivity
  have him : (conj q*c).im = Y := by
    rw [mul_comm]
    dsimp [c,Y]
    rw [sub_mul,mul_assoc,hq',mul_one]
    simp
  have repr : crossSource a q z =
      ((2*a*(1-a)*Y : ℝ):ℂ) * (Complex.I * (conj q*c)) / ((R*‖c‖^2:ℝ):ℂ) := by
    have hcconj : conj z - (a:ℂ)*conj q = conj c := by simp [c]
    rw [crossSource_formula hz hd hc,hcconj]
    change 2*Complex.I*(a:ℂ)*(1-a)*conj q*(Y:ℂ) / ((R:ℂ)*conj c) = _
    have hden : ((R*‖c‖^2:ℝ):ℂ) = (R:ℂ)*(c*conj c) := by
      rw [Complex.ofReal_mul,coe_sq_norm]
    rw [hden]
    push_cast
    field_simp
  rw [repr,Complex.div_ofReal_re,Complex.re_ofReal_mul,Complex.I_mul_re,him]
  dsimp [Y,R,c]
  ring

theorem crossSource_abs {a : ℝ} {q z : ℂ} (ha : 0 ≤ a) (hb : a ≤ 1) (hq : ‖q‖ = 1)
    (hz : z ≠ 0) (hd : z-q ≠ 0) (hc : z-(a:ℂ)*q ≠ 0) :
    ‖crossSource a q z‖ = 2*a*(1-a)*|(z*conj q).im| /
      (‖z‖^2*‖z-q‖^2*‖z-(a:ℂ)*q‖) := by
  rw [crossSource_formula hz hd hc]
  have conjdiff : conj z - (a:ℂ)*conj q = conj (z-(a:ℂ)*q) := by simp
  rw [conjdiff]
  have habs : ‖1-(a:ℂ)‖ = 1-a := by
    have h : (1:ℂ)-(a:ℂ) = ((1-a:ℝ):ℂ) := by push_cast; rfl
    rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hb)]
  have hR : 0 ≤ ‖z‖^2*‖z-q‖^2 := by positivity
  simp only [norm_div,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_conj, hq, habs, abs_of_nonneg ha, abs_of_nonneg hR, one_mul, mul_one]
  norm_num

end Liu
