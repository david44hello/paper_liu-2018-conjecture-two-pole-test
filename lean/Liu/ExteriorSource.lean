import Liu.FrozenFieldLimit
import Liu.WitnessAsymptotic

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate Topology
namespace Liu

/-- Logarithm of the exterior model with the upper-half-plane argument on both edges. -/
def exteriorLog (m : ℝ) (z : ℂ) : ℂ :=
  (log (m/‖z‖):ℂ)+((π-z.arg:ℝ):ℂ)*Complex.I

theorem PickSum.exterior_log_error {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∃ T>1, ∀ z : ℂ, 0≤z.im → T≤‖z‖ →
      ‖Complex.log (p.value z)-exteriorLog p.mass z‖≤C/‖z‖ := by
  obtain ⟨A,hA,T,hT,ha⟩ := p.argument_far
  let B := p.farBound/p.mass
  have hm := p.mass_pos
  have hfar : 0≤p.farBound := by simpa using (norm_nonneg _).trans (p.far_remainder (z:=0) (by simp))
  have hB : 0≤B := div_nonneg hfar hm.le
  refine ⟨(3/2)*B+A,by positivity,max T (2*B),hT.trans_le (le_max_left ..),?_⟩
  intro z hz hmax
  have hTz := (le_max_left ..).trans hmax
  have hr := zero_lt_one.trans (hT.trans_le hTz)
  have hn := norm_pos_iff.mp hr
  have hS : p.value z≠0 := fun he => by have hi := p.value_im_pos hz; simp [he] at hi
  let a := -(p.mass:ℂ)/z
  have han : a≠0 := div_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hm.ne')) hn
  have hanorm : ‖a‖=p.mass/‖z‖ := by simp [a,norm_div,abs_of_pos hm]
  let u := p.value z/a
  have hid : u-1=-(z*p.value z+(p.mass:ℂ))/(p.mass:ℂ) := by
    dsimp [u,a]; field_simp [hn,Complex.ofReal_ne_zero.mpr hm.ne']; ring
  have hsmall : ‖u-1‖≤B/‖z‖ := by
    rw [hid,norm_div,norm_neg,Complex.norm_of_nonneg hm.le]
    apply (div_le_div_of_nonneg_right (p.far_remainder hz) hm.le).trans
    calc
      _ ≤ (p.farBound/‖z‖)/p.mass := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left hfar hr (by linarith)) hm.le
      _ = _ := by dsimp [B]; ring
  have hh := Complex.norm_log_one_add_half_le_self (hsmall.trans ((div_le_iff₀ hr).mpr (by linarith [(le_max_right ..).trans hmax])))
  rw [show 1+(u-1)=u by ring] at hh
  have hreal : (Complex.log (p.value z)-exteriorLog p.mass z).re=(Complex.log u).re := by
    simp [exteriorLog,Complex.log_re,u,norm_div,Real.log_div (norm_ne_zero_iff.mpr hS) (norm_ne_zero_iff.mpr han),hanorm]
    rw [Real.log_div (norm_ne_zero_iff.mpr hS) (div_ne_zero hm.ne' hr.ne')]
  have him : (Complex.log (p.value z)-exteriorLog p.mass z).im=(p.value z).arg-(π-z.arg) := by simp [exteriorLog,Complex.log_im]
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  rw [hreal,him]
  have hl := (Complex.abs_re_le_norm _).trans (hh.trans (mul_le_mul_of_nonneg_left hsmall (by norm_num)))
  exact (add_le_add hl (ha z hz hTz)).trans_eq (by ring)

/-- Uniform cubic error for the actual frozen source, with the full phase of its far model. -/
def exteriorFrozenSource (m t : ℝ) (z : ℂ) : ℂ :=
  ((1+t:ℝ):ℂ)*conj (Complex.exp (exteriorLog m z*(t:ℂ)))*((m/(2*‖z‖^2):ℝ):ℂ)

theorem PickSum.exterior_frozen_source_error {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∃ T>1, ∀ t ∈ Icc (0:ℝ) 1, ∀ z : ℂ, 0≤z.im → T≤‖z‖ →
      ‖p.frozenLogSource t z-exteriorFrozenSource p.mass t z‖ ≤ C/‖z‖^3 := by
  obtain ⟨A,hA,T,hT,ha⟩ := p.exterior_log_error
  obtain ⟨B,hB,hb⟩ := p.source_far_model
  let M := max 1 p.mass
  have hm := p.mass_pos
  have hM : 1≤M := le_max_left ..
  have hMp := zero_lt_one.trans_le hM
  let P := max 1 p.bound
  have hP : 1≤P := le_max_left ..
  have hPp := zero_lt_one.trans_le hP
  refine ⟨2*P*B+2*M*A*p.mass,by positivity,max T A,hT.trans_le (le_max_left ..),?_⟩
  intro t ht z hz hmax
  have hTz := (le_max_left ..).trans hmax
  have hr1 := hT.trans_le hTz
  have hr := zero_lt_one.trans hr1
  have hS : p.value z≠0 := fun he => by have hi := p.value_im_pos hz; simp [he] at hi
  let a := Complex.exp (exteriorLog p.mass z*(t:ℂ))
  let b := (Complex.log (p.value z)-exteriorLog p.mass z)*(t:ℂ)
  have hbnd : ‖b‖≤A/‖z‖ := by
    dsimp only [b]; rw [norm_mul,Complex.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right (ha z hz hTz) ht.1).trans (mul_le_of_le_one_right (by positivity) ht.2)
  have he := Complex.norm_exp_sub_one_le (hbnd.trans ((div_le_one hr).mpr ((le_max_right ..).trans hmax)))
  have ham : ‖a‖ ≤ M := by
    dsimp only [a]
    rw [Complex.norm_exp]
    have eqn : (exteriorLog p.mass z*(t:ℂ)).re=log (p.mass/‖z‖)*t := by simp [exteriorLog,Complex.mul_re]
    rw [eqn,←rpow_def_of_pos (div_pos hm hr)]
    apply (rpow_le_rpow (by positivity) ((div_le_self hm.le hr1.le).trans (le_max_right ..)) ht.1).trans
    exact (rpow_le_rpow_of_exponent_le hM ht.2).trans_eq (rpow_one _)
  have val : p.power t z=a*Complex.exp b := by
    rw [PickSum.power,Complex.cpow_def_of_ne_zero hS]
    dsimp only [a,b]; rw [←Complex.exp_add]; congr 1; ring
  have hd : ‖p.power t z-a‖ ≤ (2*M*A)/‖z‖ := by
    rw [val,show a*Complex.exp b-a=a*(Complex.exp b-1) by ring,norm_mul]
    apply (mul_le_mul ham (he.trans (mul_le_mul_of_nonneg_left hbnd (by norm_num))) (norm_nonneg _) hMp.le).trans_eq
    ring
  have hpow : ‖p.power t z‖ ≤ P := by
    change ‖p.value z^(t:ℂ)‖≤P
    rw [Complex.norm_cpow_real]
    have hv := (p.global_decay hz).trans ((div_le_self p.bound_pos.le (by linarith [norm_nonneg z])).trans (le_max_right 1 p.bound))
    exact (rpow_le_rpow (norm_nonneg _) hv ht.1).trans ((rpow_le_rpow_of_exponent_le hP ht.2).trans_eq (rpow_one _))
  let c : ℂ := ((p.mass/(2*‖z‖^2):ℝ):ℂ)
  have hc : ‖c‖=p.mass/(2*‖z‖^2) := Complex.norm_of_nonneg (by positivity)
  have hs : ‖-Complex.I*source p.value z-c‖ ≤ B/‖z‖^3 := by
    have hid : -Complex.I*source p.value z-c = -Complex.I*(source p.value z-Complex.I*c) := by ring_nf; simp [Complex.I_sq,sub_eq_add_neg]
    rw [hid,norm_mul,norm_neg,Complex.norm_I,one_mul]
    exact hb z hz hr1
  let d := ((1+t:ℝ):ℂ)
  have hdn : ‖d‖≤2 := by rw [show ‖d‖=1+t from Complex.norm_of_nonneg (by linarith [ht.1])]; linarith [ht.2]
  have hid : p.frozenLogSource t z-exteriorFrozenSource p.mass t z =
      d*(conj (p.power t z)*(-Complex.I*source p.value z-c)+conj (p.power t z-a)*c) := by
    rw [p.frozenSource_factor t hz]
    simp only [exteriorFrozenSource,PickSum.parameterFactor,map_mul,Complex.conj_ofReal,map_sub,d,a,c]; ring
  rw [hid,norm_mul]
  apply (mul_le_mul hdn (norm_add_le ..) (norm_nonneg _) (by norm_num)).trans
  simp only [norm_mul,Complex.norm_conj,hc]
  apply (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul hpow hs (norm_nonneg _) hPp.le)
    (mul_le_mul_of_nonneg_right hd (by positivity : 0≤p.mass/(2*‖z‖^2)))) (by norm_num : (0:ℝ)≤2)).trans_eq
  field_simp [hr.ne']

end Liu
