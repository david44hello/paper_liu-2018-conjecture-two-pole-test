module

public import Liu.FarFieldClaim
public import Liu.CanonicalField
public import Liu.Orthogonality

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter
open scoped ComplexConjugate Topology
namespace Liu

private theorem arg_div_principal {a b : ℂ} (ha : a≠0) (hb : b≠0)
    (h : a.arg-b.arg∈Ioc (-π) π) : (a/b).arg=a.arg-b.arg := by
  have eqn := congrArg Real.Angle.toReal (Complex.arg_div_coe_angle ha hb)
  simpa only [Complex.arg_coe_angle_toReal_eq_arg,←Real.Angle.coe_sub,Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr h] using eqn

theorem PickSum.argument_far {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∃ T > 1, ∀ z : ℂ, 0≤z.im → T≤‖z‖ →
      |(p.value z).arg-(π-z.arg)| ≤ C/‖z‖ := by
  let T := 2+2*p.farBound/p.mass
  have hB : 0≤p.farBound := by simpa using (norm_nonneg _).trans (p.far_remainder (z:=0) (by simp))
  have hm := p.mass_pos
  have hT : 1<T := by dsimp [T]; linarith [div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hB) hm.le]
  refine ⟨(3/2)*p.farBound/p.mass,by positivity,T,hT,?_⟩
  intro z hz hr
  let S := p.value z
  let a : ℂ := -(p.mass:ℂ)/z
  let u := S/a
  have hrp : 0<‖z‖ := zero_lt_one.trans (hT.trans_le hr)
  have hn := norm_pos_iff.mp hrp
  have hmC := Complex.ofReal_ne_zero.mpr hm.ne'
  have ha : a≠0 := div_ne_zero (neg_ne_zero.mpr hmC) hn
  have hS : S≠0 := fun e => by have hh := p.value_im_pos hz; change 0<S.im at hh; simp [e] at hh
  have hθ := Complex.arg_nonneg_iff.mpr hz
  have hπ := Complex.arg_le_pi z
  have harg : a.arg=π-z.arg := by
    have hneg : (-(p.mass:ℂ)).arg=π := by rw [←Complex.ofReal_neg,Complex.arg_ofReal_of_neg (by linarith)]
    dsimp [a]
    rw [arg_div_principal (neg_ne_zero.mpr hmC) hn (by rw [hneg]; constructor <;> linarith [pi_pos]),hneg]
  have hα := upper_arg_range (show S∈upper from p.value_im_pos hz)
  have hdiff : u.arg=S.arg-(π-z.arg) := by
    rw [show u.arg=S.arg-a.arg from arg_div_principal hS ha (by
      rw [harg]; constructor <;> linarith [hα.1,hα.2]),harg]
  have hid : u-1=-(z*S+(p.mass:ℂ))/(p.mass:ℂ) := by dsimp [u,a]; field_simp [hmC,hn]; ring
  have hcmp : ‖u-1‖ ≤ (p.farBound/p.mass)/‖z‖ := by
    rw [hid,norm_div,norm_neg,Complex.norm_of_nonneg hm.le]
    apply (div_le_div_of_nonneg_right (p.far_remainder hz) hm.le).trans
    calc
      _ ≤ (p.farBound/‖z‖)/p.mass := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left hB hrp (by linarith)) hm.le
      _ = _ := by ring
  have hsmall : ‖u-1‖≤1/2 := hcmp.trans (by
    apply (div_le_iff₀ hrp).mpr
    dsimp only [T] at hr
    rw [mul_div_assoc] at hr
    linarith)
  have hlog := Complex.norm_log_one_add_half_le_self hsmall
  rw [show 1+(u-1)=u by ring] at hlog
  rw [←hdiff,←Complex.log_im]
  apply (Complex.abs_im_le_norm _).trans (hlog.trans _)
  apply (mul_le_mul_of_nonneg_left hcmp (by norm_num : 0≤(3/2:ℝ))).trans_eq
  ring

theorem PickSum.optimalWitness_isWitness {n : ℕ} (p : PickSum n) : isWitness (optimalWitness p.value) := by
  have hwh := p.optimalWitness_holomorphic
  have hval (z : ℂ) (hz : 0≤z.im) : p.value z≠0 := fun he => by have hh := p.value_im_pos hz; simp [he] at hh
  have hcS : ContinuousOn p.value {z : ℂ | 0≤z.im} := fun z hz => (p.hasDerivAt hz).continuousAt.continuousWithinAt
  have harg : ContinuousOn (fun w => (p.value w).arg) {z : ℂ | 0≤z.im} := by
    intro z hz
    exact (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr (Or.inr (p.value_im_pos hz).ne'))).comp_continuousWithinAt (hcS z hz)
  refine ⟨hwh,((hcS.mul (Complex.continuous_ofReal.comp_continuousOn harg)).sub p.field_continuous_closed).div hcS hval,?_⟩
  obtain ⟨A,hA,T,hT,ha⟩ := p.argument_far
  obtain ⟨B,hB,hb⟩ := p.field_far_estimate
  obtain ⟨c,hc,hc'⟩ := p.two_sided_decay
  let P := A+2*(B+π*p.farBound)/c
  have hP : 0≤p.farBound := by simpa using (norm_nonneg _).trans (p.far_remainder (z:=0) (by simp))
  refine ⟨1+P,by dsimp only [P]; positivity,T,zero_lt_one.trans hT,?_⟩
  intro z hz hr
  let r := ‖z‖
  have hr1 := hT.trans_le hr
  have hp := zero_lt_one.trans hr1
  have hrpos : 0<r := hp
  have hlogr : 0≤log r := log_nonneg hr1.le
  have hn := norm_pos_iff.mp hp
  let S := p.value z
  let v := field p.value z
  let a := (π/2-z.arg)
  let b := -(p.mass:ℂ)/z
  have he : fieldFarModel p.mass z=(a:ℂ)*b := by unfold fieldFarModel; dsimp only [a,b]; push_cast; ring
  have hθ := Complex.arg_nonneg_iff.mpr hz
  have hπ := Complex.arg_le_pi z
  have hα : |a| ≤ π := abs_le.mpr ⟨by dsimp [a]; linarith [pi_pos],by dsimp [a]; linarith [pi_pos]⟩
  have hlog := log_nonneg hr1.le
  have hS : ‖S-b‖ ≤ p.farBound/r^2 := by
    rw [show S-b=(z*S+(p.mass:ℂ))/z by dsimp [b]; field_simp [hn]; ring,norm_div]
    apply (div_le_div_of_nonneg_right (p.far_remainder hz) hp.le).trans
    calc
      _ ≤ (p.farBound/r)/r := div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hP hp (by dsimp [r]; linarith)) hp.le
      _ = _ := by ring
  have hv : ‖v-(a:ℂ)*S‖ ≤ (B+π*p.farBound)*(1+log r)/r^2 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub v ((a:ℂ)*b) ((a:ℂ)*S)
    rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_sub_rev b S] at hh
    have hf := hb z hz hr1
    rw [he] at hf
    apply (hh.trans (add_le_add hf (mul_le_mul hα hS (norm_nonneg _) pi_pos.le))).trans
    change B*(1+log r)/r^2+π*(p.farBound/r^2) ≤ _
    field_simp [hrpos.ne']; nlinarith only [mul_nonneg (mul_nonneg pi_pos.le hP) hlogr]
  have hquot : ‖(v-(a:ℂ)*S)/S‖ ≤ (2*(B+π*p.farBound)/c)*(1+log r)/r := by
    rw [norm_div]
    have hlow := (hc' z hz).1
    apply (div_le_div₀ (by positivity : 0≤(B+π*p.farBound)*(1+log r)/r^2) hv (div_pos hc (by positivity)) hlow).trans
    have hW : 0<1+r := by positivity
    change _/(c/(1+r)) ≤ _
    field_simp [hc.ne',hrpos.ne',hW.ne']
    <;> nlinarith only [mul_le_mul_of_nonneg_left (show 1+r≤2*r by linarith)
      (show 0≤B+π*p.farBound by positivity)]
  have hform : optimalWitness p.value z-(π/2:ℝ) =
      (((S.arg-(π-z.arg):ℝ):ℂ))-(v-(a:ℂ)*S)/S := by
    unfold optimalWitness
    dsimp only [S,v,a]
    push_cast
    field_simp [hval z hz] <;> ring
  rw [hform]
  apply (norm_sub_le ..).trans
  rw [Complex.norm_real,Real.norm_eq_abs]
  apply (add_le_add (ha z hz hr) hquot).trans
  change A/r+_* (1+log r)/r ≤ (1+P)*(1+log r)/r
  dsimp only [P]
  field_simp [hc.ne',hrpos.ne']
  <;> nlinarith only [mul_nonneg (mul_nonneg hA hc.le) hlogr,mul_nonneg hc.le hlogr,hc.le]

end Liu
