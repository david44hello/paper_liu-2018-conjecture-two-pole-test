import Liu.SlopeFormula
import Liu.TraceSlices

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

def unitPolePick := singlePick 1 0 1 zero_lt_one zero_lt_one

theorem unitPolePick_value : unitPolePick.value=pole 1 (-Complex.I) := by
  simpa [unitPolePick] using singlePick_value 1 0 1 zero_lt_one zero_lt_one

theorem unitPolePick_mass : unitPolePick.mass=1 := by simp [unitPolePick,singlePick,PickSum.mass]

/-- All mass, depth and real-position dependence of the one-pole deficit. -/
theorem singlePole_deficit_normalization {a : ℝ} {w : ℂ} (ha : 0<a) (hw : w.im<0) :
    deficit (pole a w)=a^2*deficit unitPolePick.value := by
  let b := -w.im
  have hb : 0<b := neg_pos.mpr hw
  let q := singlePick 1 0 b zero_lt_one hb
  let s := singlePick 1 w.re b zero_lt_one hb
  have hw' : ((w.re:ℝ):ℂ)-(b:ℂ)*Complex.I=w := by dsimp [b]; apply Complex.ext <;> simp
  have hs : s.value=pole 1 w := by rw [singlePick_value,hw']
  have hq : q.value=pole 1 (-((b:ℝ):ℂ)*Complex.I) := by simp [q,singlePick_value]
  have shift : (fun z => q.value (z-(w.re:ℂ)))=s.value := by
    rw [hs,hq,←hw']
    funext z
    dsimp [pole]; simp; ring_nf
  have dil : (fun z => ((b⁻¹:ℝ):ℂ)*unitPolePick.value (z/(b:ℂ)))=q.value := by
    rw [unitPolePick_value,hq]
    funext z
    have hn : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
    have hdiv : z/(b:ℂ)- -Complex.I=(z-(-(b:ℂ)*Complex.I))/(b:ℂ) := by field_simp
    simp only [pole,hdiv,div_div_eq_mul_div,Complex.ofReal_one,Complex.ofReal_inv,div_eq_mul_inv]
    field_simp [hn]
  have mass : (fun z => (a:ℂ)*s.value z)=pole a w := by rw [hs]; funext z; simp [pole]; ring
  have h₁ := s.finite_part_laws.2.2.2.2 a
  have h₂ := (q.finite_part_laws.2.1 w.re).2
  have h₃ := unitPolePick.finite_part_laws.2.2.1 b hb
  rw [mass] at h₁
  rw [shift] at h₂
  rw [dil] at h₃
  rw [h₁,h₂,h₃]

theorem coincidentDeficit_iff_unit : coincidentDeficit ↔ deficit unitPolePick.value=singleConstant := by
  constructor
  · intro h
    simpa [unitPolePick_value] using h 1 (-Complex.I) zero_lt_one (by simp)
  · intro h a w ha hw
    rw [singlePole_deficit_normalization ha hw,h,mul_comm]

/-- The phase relating the normalized pole power to the cap in Appendix A. -/
theorem unitPole_power_phase (u : ℝ) {z : ℂ} (hz : z∈upper) :
    unitPolePick.power u z=Complex.exp ((u:ℂ)*(π:ℂ)*Complex.I)*(z+Complex.I)^(-(u:ℂ)) := by
  let v := z+Complex.I
  have hv : v∈upper := by change 0<z.im+1; linarith [show 0<z.im from hz]
  obtain ⟨hp,hπ⟩ := upper_arg_range hv
  have hn : v≠0 := fun he => by simpa [he,upper] using hv
  have hy : -1/v≠(0:ℂ) := div_ne_zero (by norm_num) hn
  have harg : (-1/v).arg=π-v.arg := by
    have he := congrArg Real.Angle.toReal (Complex.arg_div_coe_angle (by norm_num : (-1:ℂ)≠0) hn)
    simpa only [Complex.arg_coe_angle_toReal_eq_arg,←Real.Angle.coe_sub,Complex.arg_neg_one,
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr (show π-v.arg∈Ioc (-π) π by constructor <;> linarith [pi_pos])] using he
  have hlog : Complex.log (-1/v)=(π:ℂ)*Complex.I-Complex.log v := by
    apply Complex.ext <;> simp [Complex.log_re,Complex.log_im,harg,norm_div,Real.log_inv]
  rw [PickSum.power,unitPolePick_value]
  simp only [pole,Complex.ofReal_one,sub_neg_eq_add]
  change (-1/v)^(u:ℂ)=Complex.exp _*v^(-(u:ℂ))
  rw [Complex.cpow_def_of_ne_zero hy,Complex.cpow_def_of_ne_zero hn,hlog,←Complex.exp_add]
  congr 1; ring

theorem quotient_eq_of_unit_phase {f g : ℂ → ℂ} {c : ℂ} (hc : ‖c‖=1)
    (hf : MemLp f 2 upperArea) (hl : MemLp (logInput f) 2 upperArea)
    (he : EqOn g (c • f) upper) : quotient g=quotient f := by
  have hae : g =ᵐ[upperArea] c • f := (ae_restrict_iff' upper_open.measurableSet).mpr (ae_of_all _ he)
  have hlog : logInput g =ᵐ[upperArea] c • logInput f := by
    filter_upwards [hae] with z hz
    simp only [logInput,hz,Pi.smul_apply,smul_eq_mul,norm_mul,hc,one_mul]; ring
  have hg := (memLp_congr_ae hae).mpr (hf.const_smul c)
  have hh := (memLp_congr_ae hlog).mpr (hl.const_smul c)
  have eqLp {v w : ℂ → ℂ} (hv : MemLp v 2 upperArea) (hw : MemLp w 2 upperArea) (h : v=ᵐ[upperArea] w) :
      asL2 v=asL2 w := by
    simp only [asL2,dif_pos hv,dif_pos hw]
    apply Lp.ext
    exact hv.coeFn_toLp.trans (h.trans hw.coeFn_toLp.symm)
  dsimp only [quotient]
  rw [eqLp hg (hf.const_smul c) hae,eqLp hh (hl.const_smul c) hlog,asL2_smul c hf,asL2_smul c hl,map_smul,←smul_sub,norm_smul,norm_smul,hc,one_mul,one_mul]

def capPower (u : ℝ) (z : ℂ) := (z+Complex.I)^(-(u:ℂ))

theorem unitPole_quotient_eq_cap {u : ℝ} (hu : 1<u) : quotient (unitPolePick.power u)=quotient (capPower u) := by
  let c := Complex.exp ((u:ℂ)*(π:ℂ)*Complex.I)
  have hc : ‖c‖=1 := by simp [c,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  have hn : c≠0 := Complex.exp_ne_zero _
  symm
  apply quotient_eq_of_unit_phase (c:=c⁻¹) (by simp [hc]) (unitPolePick.power_memLp_two hu) (unitPolePick.log_power_memLp_two hu)
  intro z hz
  change capPower u z=c⁻¹*unitPolePick.power u z
  rw [unitPole_power_phase u hz]
  change capPower u z=c⁻¹*(c*capPower u z)
  rw [inv_mul_cancel_left₀ hn]

/-- Once the normalized cap slope is evaluated, the one-pole evaluation at all
locations and masses follows from the general slope formula. -/
theorem coincidentDeficit_iff_cap_slope :
    coincidentDeficit ↔ Tendsto (fun t : ℝ => (quotient (capPower (1+t))-k₀)/t) (𝓝[>] 0)
      (𝓝 (2*k₀-2*singleConstant)) := by
  have hh := unitPolePick.slope_formula.1
  rw [unitPolePick_mass,one_pow,div_one] at hh
  have hlim : Tendsto (fun t : ℝ => (quotient (capPower (1+t))-k₀)/t) (𝓝[>] 0)
      (𝓝 (2*(k₀-deficit unitPolePick.value))) := by
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht
    rw [unitPole_quotient_eq_cap (show 1<1+t by linarith [show 0<t from ht])]
  rw [coincidentDeficit_iff_unit]
  constructor
  · intro h; simpa [h,mul_sub] using hlim
  · intro h; linarith only [tendsto_nhds_unique hlim h]

end Liu
