module

public import Liu.OnePoleWitness
public import Liu.SingleTrace
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

noncomputable section
open Set Real Metric
open scoped Topology
namespace Liu

/-- Apply maximum modulus to exp(g) on large half-discs. -/
private theorem upper_re_nonpos {g : ℂ → ℂ} (hg : DiffContOnCl ℂ g upper)
    (hb : ∀ x : ℝ, (g x).re = 0)
    (hfar : ∀ ε > 0, ∃ R : ℝ, ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → ‖g z‖ ≤ ε)
    {z : ℂ} (hz : z ∈ upper) : (g z).re ≤ 0 := by
  by_contra! hp
  let ε := (g z).re / 2
  have he : 0 < ε := half_pos hp
  obtain ⟨R,hR⟩ := hfar ε he
  let T := max R (‖z‖+1)
  let D := halfDisc T
  have hDU : D ⊆ upper := inter_subset_left
  have hD : IsOpen D := upper_open.inter isOpen_ball
  have hbounded : Bornology.IsBounded D := isBounded_ball.subset inter_subset_right
  have hd := hg.mono hDU
  have hd' : DiffContOnCl ℂ (fun w => Complex.exp (g w)) D :=
    ⟨hd.1.cexp, Complex.continuous_exp.comp_continuousOn hd.2⟩
  have hboundary (w : ℂ) (hw : w ∈ frontier D) : ‖Complex.exp (g w)‖ ≤ exp ε := by
    rw [Complex.norm_exp,exp_le_exp]
    have hclosed := closure_mono hDU (frontier_subset_closure hw)
    rw [closure_upper_plane] at hclosed
    have him : 0 ≤ w.im := hclosed
    rcases him.eq_or_lt with h | h
    · have hx : (w.re : ℂ) = w := Complex.ext rfl (by simpa using h)
      rw [←hx,hb]; exact he.le
    · have ht : T ≤ ‖w‖ := by
        by_contra! hl
        have hi : w ∈ D := ⟨h,by simpa [mem_ball,dist_zero_right] using hl⟩
        exact (hD.frontier_eq ▸ hw).2 hi
      exact (Complex.re_le_norm _).trans (hR w him ((le_max_left ..).trans ht))
  have hzD : z ∈ D := ⟨hz,by
    simp only [mem_ball,dist_zero_right]
    exact (lt_add_one _).trans_le (le_max_right ..)⟩
  have hm := Complex.norm_le_of_forall_mem_frontier_norm_le hbounded hd' hboundary (subset_closure hzD)
  rw [Complex.norm_exp,exp_le_exp] at hm
  dsimp [ε] at hm; linarith

/-- A holomorphic function with real boundary values and uniform decay on the
closed upper half-plane vanishes. -/
theorem upper_eq_zero_of_real_trace {V : ℂ → ℂ} (hv : DiffContOnCl ℂ V upper)
    (hb : ∀ x : ℝ, (V x).im = 0)
    (hfar : ∀ ε > 0, ∃ R : ℝ, ∀ z : ℂ, 0 ≤ z.im → R ≤ ‖z‖ → ‖V z‖ ≤ ε) :
    EqOn V (fun _ => 0) (closure upper) := by
  have hs (s : ℝ) (hs : |s|=1) {z : ℂ} (hz : z∈upper) :
      (((s:ℂ)*Complex.I)*V z).re ≤ 0 := by
    apply upper_re_nonpos (g:=fun w => ((s:ℂ)*Complex.I)*V w) _ _ _ hz
    · exact ⟨hv.1.const_mul _,continuousOn_const.mul hv.2⟩
    · intro x; simp [Complex.mul_re,Complex.mul_im,hb]
    · intro ε he
      obtain ⟨R,hR⟩ := hfar ε he
      exact ⟨R,fun w hw hr => by simpa [norm_mul,Complex.norm_real,Real.norm_eq_abs,hs] using hR w hw hr⟩
  have him (z : ℂ) (hz : z∈upper) : (V z).im=0 := by
    have h₁ := hs 1 (by norm_num) hz
    have h₂ := hs (-1) (by norm_num) hz
    simp [Complex.mul_re] at h₁ h₂; linarith
  have hconn : IsConnected upper :=
    ⟨⟨Complex.I,by simp [upper]⟩,(convex_halfSpace_im_gt 0).isPreconnected⟩
  obtain ⟨c,hc⟩ := (hv.1.analyticOnNhd upper_open).eq_const_of_im_eq_const him upper_open hconn
  have hclosed := isClosed_closure.isClosed_eq hv.2 (continuousOn_const (c:=c))
  have hsub : upper ⊆ {z ∈ closure upper | V z=c} := fun z hz => ⟨subset_closure hz,hc z hz⟩
  have H : EqOn V (fun _ => c) (closure upper) := fun _ hz => (closure_minimal hsub hclosed hz).2
  have hc0 : c=0 := by
    by_contra hn
    have hp := norm_pos_iff.mpr hn
    obtain ⟨R,hR⟩ := hfar (‖c‖/2) (half_pos hp)
    have h := hR (R:ℂ) (by simp) (by simpa [Complex.norm_real,Real.norm_eq_abs] using le_abs_self R)
    rw [H (show (R:ℂ)∈closure upper by rw [closure_upper_plane]; simp)] at h
    dsimp only at h; linarith
  simpa [hc0] using H

private theorem unit_candidate_real (x : ℝ) :
    (unitPolePick.value x * (((unitPolePick.value x).arg:ℂ)-singleWitness x)).im = 0 := by
  let v := (x:ℂ)+Complex.I
  have hv : v∈upper := by simp [v,upper]
  have hvn : v≠0 := fun e => by simpa [e,upper] using hv
  have hxi : (x:ℂ)≠Complex.I := fun e => by simpa using congrArg Complex.im e
  have hs : unitPolePick.value x= -1/v := by simp [unitPolePick_value,pole,v]
  obtain ⟨hp,hπ⟩ := upper_arg_range hv
  have ha : (-1/v).arg=π-v.arg := by
    have he := congrArg Real.Angle.toReal (Complex.arg_div_coe_angle (by norm_num : (-1:ℂ)≠0) hvn)
    simpa only [Complex.arg_coe_angle_toReal_eq_arg,←Real.Angle.coe_sub,Complex.arg_neg_one,
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr (show π-v.arg∈Ioc (-π) π by constructor <;> linarith [pi_pos])] using he
  have hi : (Complex.I+Complex.I).arg=π/2 := by
    rw [←two_mul,show (2:ℂ)=((2:ℝ):ℂ) by norm_num,Complex.arg_real_mul _ (by norm_num),Complex.arg_I]
  let D := x^2+1
  have hD : 0<D := by dsimp [D]; positivity
  have hprod : (D:ℂ)=v*((x:ℂ)-Complex.I) := by
    dsimp [D,v]; push_cast; ring_nf; simp [Complex.I_sq,add_comm]
  let f := unitPolePick.value x * (((unitPolePick.value x).arg:ℂ)-singleWitness x)
  have hformula : (D:ℂ)*f =
      -((x:ℂ)-Complex.I)*((π/2-v.arg:ℝ):ℂ)+Complex.log v-Complex.log (Complex.I+Complex.I) := by
    dsimp only [f,singleWitness,omegaCorrection]
    rw [hs,ha,dslope_of_ne _ hxi,slope_def_field,hprod]
    change _ = _
    change (v*((x:ℂ)-Complex.I))*(-1/v*((((π-v.arg:ℝ):ℂ))-(((π/2:ℝ):ℂ)+(Complex.log v-Complex.log (Complex.I+Complex.I))/((x:ℂ)-Complex.I)))) = _
    push_cast
    field_simp [hvn,sub_ne_zero.mpr hxi] <;> ring
  have him := congrArg Complex.im hformula
  simp [Complex.mul_im,Complex.mul_re,Complex.log_im,hi] at him
  change f.im=0
  exact him.resolve_left hD.ne'

/-- The candidate and the optimal witness are identified by their physical
fields on the real axis and uniqueness in the half-plane. -/
theorem unitPole_optimalWitness {z : ℂ} (hz : 0≤z.im) :
    optimalWitness unitPolePick.value z=singleWitness z := by
  let p := unitPolePick
  let V := fun w => p.value w*(optimalWitness p.value w-singleWitness w)
  have ho := p.optimalWitness_isWitness
  have hw := singleWitness_isWitness
  have hn {w : ℂ} (h : 0≤w.im) : p.value w≠0 := fun e => by have hh := p.value_im_pos h; simp [e] at hh
  have hv : DiffContOnCl ℂ V upper := by
    refine ⟨p.holomorphic.mul (ho.1.sub hw.1),?_⟩
    rw [closure_upper_plane]
    exact (show ContinuousOn p.value {w : ℂ | 0≤w.im} from
      fun w h => (p.hasDerivAt h).continuousAt.continuousWithinAt).mul (ho.2.1.sub hw.2.1)
  have hb (x : ℝ) : (V x).im=0 := by
    have he : V x = p.value x*(((p.value x).arg:ℂ)-singleWitness x)-field p.value x := by
      dsimp [V,optimalWitness]; field_simp [hn (w:=(x:ℂ)) (by simp)] <;> ring
    have hf : field p.value x= -(isolatedTrace 0 1 x:ℂ) := by
      simpa [p,unitPolePick_value] using field_single_pole 0 x zero_lt_one zero_lt_one
    rw [he,Complex.sub_im,unit_candidate_real,hf]; simp
  obtain ⟨A,hA,T,hT,ha⟩ := ho.2.2
  let B := A+log 2
  have hB : 0≤B := by dsimp [B]; positivity
  have hdec (ε : ℝ) (he : 0<ε) : ∃ R : ℝ, ∀ w : ℂ, 0≤w.im → R≤‖w‖ → ‖V w‖≤ε := by
    refine ⟨max T (p.bound*B/ε),?_⟩
    intro w hw' hr
    have hT' := (le_max_left ..).trans hr
    have hrp := hT.trans_le hT'
    have hA' : ‖optimalWitness p.value w-((π/2:ℝ):ℂ)‖≤A :=
      (ha w hw' hT').trans ((div_le_iff₀ hrp).mpr (mul_le_mul_of_nonneg_left
        (by linarith [log_le_sub_one_of_pos hrp]) hA.le))
    have hb' := norm_sub_le_norm_sub_add_norm_sub (optimalWitness p.value w) ((π/2:ℝ):ℂ) (singleWitness w)
    have hq : ‖((π/2:ℝ):ℂ)-singleWitness w‖=‖omegaCorrection w‖ := by rw [norm_sub_rev]; simp [singleWitness]
    rw [hq] at hb'
    have hv' := mul_le_mul (p.global_decay hw') (hb'.trans (add_le_add hA' (omegaCorrection_bound hw'))) (norm_nonneg _) (by have := p.bound_pos; positivity)
    change ‖p.value w*(optimalWitness p.value w-singleWitness w)‖ ≤ ε
    rw [norm_mul]
    apply hv'.trans
    change p.bound/(1+‖w‖)*B ≤ ε
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    have h := (div_le_iff₀ he).mp ((le_max_right ..).trans hr)
    linarith
  have h := upper_eq_zero_of_real_trace hv hb hdec (show z∈closure upper by rwa [closure_upper_plane])
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (hn hz))

end Liu
