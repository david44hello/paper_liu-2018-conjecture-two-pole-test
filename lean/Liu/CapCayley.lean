module

public import Liu.DiscBinomial
public import Liu.CapExpansion

@[expose] public section

noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate Topology
namespace Liu

def discLog (w : ℂ) := Complex.log (1-w)
def capFactor (α : ℝ) : ℂ := (2*Complex.I)*(2*Complex.I)^(-(α:ℂ))

theorem cap_cayley_log {w : ℂ} (hw : w∈disc) :
    Complex.log (cayley Complex.I w+Complex.I)=Complex.log (2*Complex.I)-discLog w := by
  have hn : ‖w‖<1 := by simpa [disc] using hw
  have hre : 0<(1-w).re := by simp only [Complex.sub_re,Complex.one_re]; linarith [Complex.re_le_norm w]
  have h1 : 1-w≠0 := fun he => by simp [he] at hre
  have h2 : (2:ℂ)*Complex.I≠0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have he : cayley Complex.I w+Complex.I=2*Complex.I/(1-w) := by unfold cayley; rw [Complex.conj_I]; field_simp; ring
  rw [he]; apply Complex.ext
  · simp [Complex.log_re,discLog,norm_div,log_div (by norm_num : (2:ℝ)≠0) (norm_ne_zero_iff.mpr h1)]
  · have harg := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    have hlow := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hre)
    have htwo : ((2:ℂ)*Complex.I).arg=π/2 := by
      rw [show (2:ℂ)*Complex.I=((2:ℝ):ℂ)*Complex.I by norm_num,Complex.arg_real_mul _ (by norm_num),Complex.arg_I]
    have hh : (2*Complex.I).arg-(1-w).arg∈Ioc (-π) π := by rw [htwo]; constructor <;> linarith [pi_pos]
    have e := congrArg Real.Angle.toReal (Complex.arg_div_coe_angle h2 h1)
    simp only [Complex.arg_coe_angle_toReal_eq_arg,←Real.Angle.coe_sub,Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hh] at e
    simpa only [Complex.log_im,Complex.sub_im,discLog] using e

theorem cap_cayley_pull (α : ℝ) {w : ℂ} (hw : w∈disc) :
    cayleyPull Complex.I (capPower α) w=capFactor α*discPower (2-α) w := by
  have hn : 1-w≠0 := by intro he; rw [←sub_eq_zero.mp he] at hw; simpa [disc] using hw
  have h2 : 2*Complex.I≠0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hU := (cayley_bijOn (show Complex.I∈upper by simp [upper])).mapsTo hw
  have hv : cayley Complex.I w+Complex.I≠0 := by
    intro he; have h := congrArg Complex.im he; simp at h
    linarith [show 0<(cayley Complex.I w).im from hU]
  have hj : cayleyJac Complex.I w=(2*Complex.I)/(1-w)^2 := by simp [cayleyJac,sub_neg_eq_add,two_mul]
  have hnorm : (1-w)^2=Complex.exp (discLog w*2) := by
    rw [mul_two,Complex.exp_add,discLog,Complex.exp_log hn,pow_two]
  rw [cayleyPull,capPower,capFactor,discPower,Complex.cpow_def_of_ne_zero hv,cap_cayley_log hw,hj,hnorm,
    Complex.cpow_def_of_ne_zero h2,Complex.cpow_def_of_ne_zero hn]
  dsimp only [discLog]; push_cast
  let A := Complex.log (2*Complex.I)
  let L := Complex.log (1-w)
  change Complex.exp ((A-L)* -(α:ℂ))*(2*Complex.I/Complex.exp (L*2)) =
    2*Complex.I*Complex.exp (A* -(α:ℂ))*(1/Complex.exp (L*(2-(α:ℂ))))
  calc
    _ = (2*Complex.I)*Complex.exp (((A-L)* -(α:ℂ)) + -(L*2)) := by rw [Complex.exp_add,Complex.exp_neg]; ring
    _ = (2*Complex.I)*Complex.exp ((A* -(α:ℂ)) + -(L*(2-(α:ℂ)))) := by congr 2; ring
    _ = _ := by rw [Complex.exp_add,Complex.exp_neg]; ring

theorem cap_cayley_log_norm (α : ℝ) {w : ℂ} (hw : w∈disc) :
    log ‖capPower α (cayley Complex.I w)‖=α*(discLog w).re-α*log 2 := by
  have hn := (cayley_bijOn (show Complex.I∈upper by simp [upper])).mapsTo hw
  have hv : cayley Complex.I w+Complex.I≠0 := by
    intro e; have h := congrArg Complex.im e; simp at h
    linarith [show 0<(cayley Complex.I w).im from hn]
  rw [capPower,Complex.cpow_def_of_ne_zero hv,Complex.norm_exp,Real.log_exp,cap_cayley_log hw]
  simp [Complex.mul_re,Complex.log_re,discLog]; ring

theorem cap_cayley_logInput (α : ℝ) {w : ℂ} (hw : w∈disc) :
    cayleyPull Complex.I (logInput (capPower α)) w=capFactor α*
      (((α:ℂ)/2)*discPower (2-α) w*discLog w+((α:ℂ)/2)*discPower (2-α) w*conj (discLog w)
        -((α*log 2:ℝ):ℂ)*discPower (2-α) w) := by
  have he : cayleyPull Complex.I (logInput (capPower α)) w=
      cayleyPull Complex.I (capPower α) w*(log ‖capPower α (cayley Complex.I w)‖:ℝ) := by
    dsimp [cayleyPull,logInput]; ring
  rw [he,cap_cayley_pull α hw,cap_cayley_log_norm α hw]
  push_cast
  have h := Complex.add_conj (discLog w)
  push_cast at h
  linear_combination (norm := ring) -(capFactor α*(α:ℂ)/2*discPower (2-α) w)*h

end Liu
