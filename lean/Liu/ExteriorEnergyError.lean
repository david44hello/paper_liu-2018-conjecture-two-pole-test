import Liu.PhysicalExterior
import Liu.ModelEnergy
import Liu.CompactFrozenEnergy

noncomputable section
open Set MeasureTheory Real Filter Metric
open scoped Topology ComplexConjugate
namespace Liu

def PickSum.frozenDensity {n : ℕ} (p : PickSum n) (t : ℝ) (z : ℂ) :=
  ‖canonicalField (p.frozenLogSource t) z‖^2-k₀*‖p.power (1+t) z‖^2

private theorem logTail_comparison {r : ℝ} (hr : 1≤r) :
    (1+log r)/r^3 ≤ 8*((1+log (2+r))/(1+r)^3) := by
  have hp := zero_lt_one.trans_le hr
  have hl := log_le_log hp (show r≤2+r by linarith)
  have hgeom := pow_le_pow_left₀ (by positivity : 0≤1+r) (by linarith : 1+r≤2*r) 3
  have hh : (1+r)^3≤8*r^3 := by nlinarith only [hgeom]
  apply (div_le_div_of_nonneg_right (add_le_add le_rfl hl) (pow_nonneg hp.le 3)).trans
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos hp 3) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hh (by have := log_nonneg (by linarith : 1≤2+r); linarith : 0≤1+log (2+r))]

private theorem square_field_error {v u : ℂ} {r K D : ℝ} (hr : 1≤r) (hK : 0≤K) (hD : 0≤D)
    (he : ‖v-u‖≤K*(1+log r)/r^2) (hu : ‖u‖≤D/r) :
    |‖v‖^2-‖u‖^2| ≤ K*(K+2*D)*((1+log r)/r^3) := by
  have hp := zero_lt_one.trans_le hr
  have he' : ‖v-u‖≤K/r := he.trans (by
    apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith [log_le_sub_one_of_pos hp] : 1+log r≤r) hK) hp.le])
  have hv : ‖v‖≤(K+D)/r := by
    have hh := norm_add_le (v-u) u
    rw [sub_add_cancel] at hh
    exact hh.trans ((add_le_add he' hu).trans_eq (add_div ..).symm)
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),mul_comm (‖v‖+‖u‖)]
  have hsum : ‖v‖+‖u‖≤(K+2*D)/r := (add_le_add hv hu).trans_eq (by ring)
  apply (mul_le_mul ((abs_norm_sub_norm_le ..).trans he) hsum (by positivity) (by have := log_nonneg hr; positivity)).trans_eq
  field_simp [hp.ne'] <;> ring

theorem PickSum.frozen_energy_tail_error {n : ℕ} (p : PickSum n) :
    ∃ L ≥ 0, ∀ t : ℝ, 0<t → t<1 → t*π≤1/2 → ∀ z : ℂ, 0≤z.im → 2<‖z‖ →
      |p.frozenDensity t z-modelEnergyDensity p.mass t z| ≤ L*logTail z := by
  obtain ⟨K,hK,hf⟩ := p.frozen_exterior_field_error
  obtain ⟨A,hA,ha⟩ := p.power_tail_error
  let D := (max 1 p.mass)^2*(8*π^2+8*π)
  have hD : 0≤D := by dsimp [D]; positivity
  have hk : 0≤k₀ := by unfold k₀; positivity
  let L := K*(K+2*D)+k₀*A
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨L*8,by positivity,?_⟩
  intro t ht ht1 hs z hz hr
  let r := ‖z‖
  have hr1 : 1≤r := by dsimp [r]; linarith
  have hp := zero_lt_one.trans_le hr1
  let u := exteriorField p.mass t z
  let v := canonicalField (p.frozenLogSource t) z
  have hu : ‖u‖≤D/r := by
    rw [show ‖u‖=_ from exteriorField_norm p.mass_pos t z]
    have hpow : p.mass^(1+t)≤(max 1 p.mass)^2 := by
      apply (rpow_le_rpow p.mass_pos.le (le_max_right ..) (by linarith : 0≤1+t)).trans
      simpa only [rpow_ofNat] using rpow_le_rpow_of_exponent_le (le_max_left 1 p.mass) (by linarith : 1+t≤(2:ℝ))
    have hrt := rpow_le_one_of_one_le_of_nonpos hr1 (by linarith : -t≤0)
    have hv := modelAngularFlux_bound ht ht1 hs (show z.arg∈Icc 0 π from ⟨Complex.arg_nonneg_iff.mpr hz,Complex.arg_le_pi _⟩)
    apply (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr hp.le)) hrt (rpow_nonneg hp.le _) (by positivity)) hv (norm_nonneg _) (by positivity)).trans_eq
    dsimp [D,r]; ring
  have herr := square_field_error hr1 hK hD (hf t ht ht1 hs z hz hr) hu
  let q := 2+2*t
  have hs' := ha q (show q∈Icc 2 4 by dsimp [q]; constructor <;> linarith) z hz (by linarith)
  have hpow : ‖p.power (1+t) z‖^2=‖p.value z‖^q := by
    change ‖p.value z^((1+t:ℝ):ℂ)‖^2=_
    rw [Complex.norm_cpow_real,←rpow_ofNat (‖p.value z‖^(1+t)) 2,←rpow_mul (norm_nonneg _)]
    dsimp [q]; congr 1; ring
  have eqn : p.frozenDensity t z-modelEnergyDensity p.mass t z =
      (‖v‖^2-‖u‖^2)-k₀*(‖p.value z‖^q-p.mass^q*r^(-q)) := by
    dsimp only [PickSum.frozenDensity,modelEnergyDensity,v,u,r,q]
    rw [exteriorField_sq p.mass_pos t (norm_pos_iff.mp hp),hpow]; dsimp only [q]; ring
  rw [eqn]
  apply (abs_sub ..).trans
  rw [abs_mul,abs_of_nonneg hk]
  apply (add_le_add herr (mul_le_mul_of_nonneg_left hs' hk)).trans
  have hlog : 1≤1+log r := by linarith [log_nonneg hr1]
  have hx : A*‖z‖^(-(3:ℝ)) ≤ A*((1+log r)/r^3) := by
    rw [rpow_neg hp.le,rpow_ofNat]
    apply mul_le_mul_of_nonneg_left _ hA
    simpa only [one_div] using div_le_div_of_nonneg_right hlog (pow_nonneg hp.le 3)
  calc
    _ ≤ K*(K+2*D)*((1+log r)/r^3)+k₀*(A*((1+log r)/r^3)) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hx hk)
    _ = L*((1+log r)/r^3) := by dsimp [L]; ring
    _ ≤ L*(8*logTail z) := mul_le_mul_of_nonneg_left (logTail_comparison hr1) hL
    _ = _ := by ring

end Liu
