import Liu.PowerSource
import Liu.KernelControl

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

def PickSum.parameterFactor {n : ℕ} (p : PickSum n) (t : ℝ) (z : ℂ) : ℂ :=
  ((1+t:ℝ):ℂ)*p.power t z

def PickSum.parameterSlope {n : ℕ} (p : PickSum n) (t : ℝ) (z : ℂ) : ℂ :=
  p.power t z*(1+((1+t:ℝ):ℂ)*Complex.log (p.value z))

theorem PickSum.parameterFactor_hasDerivAt {n : ℕ} (p : PickSum n) (t : ℝ) {z : ℂ} (hz : 0≤z.im) :
    HasDerivAt (fun s => p.parameterFactor s z) (p.parameterSlope t z) t := by
  have hn : p.value z ≠ 0 := fun he => by have hi := p.value_im_pos hz; simp [he] at hi
  have hp := (Complex.hasStrictDerivAt_const_cpow (y:=(t:ℂ)) (Or.inl hn)).hasDerivAt.comp_ofReal
  have h₁ := ((hasDerivAt_id t).const_add 1).ofReal_comp
  convert h₁.mul hp using 1
  · rfl
  · simp [PickSum.parameterSlope,PickSum.power]; ring

theorem PickSum.parameterSlope_bound {n : ℕ} (p : PickSum n) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ z : ℂ, 0≤z.im →
      ‖p.parameterSlope t z‖ ≤ C*(1+log (2+‖z‖)) := by
  obtain ⟨B,hB,hlog⟩ := p.log_power_growth (by norm_num : (0:ℝ)<1)
  let M := max 1 p.bound
  have hm : 1≤M := le_max_left ..
  have hM := zero_lt_one.trans_le hm
  refine ⟨M*(1+2*(B+π)+2),by positivity,?_⟩
  intro t ht z hz
  have hv := (p.global_decay hz).trans
    ((div_le_self p.bound_pos.le (by linarith [norm_nonneg z])).trans (le_max_right 1 p.bound))
  have hp : ‖p.power t z‖ ≤ M := by
    change ‖p.value z^(t:ℂ)‖ ≤ M
    rw [Complex.norm_cpow_real]
    exact (rpow_le_rpow (norm_nonneg _) hv ht.1).trans ((rpow_le_rpow_of_exponent_le hm ht.2).trans_eq (rpow_one _))
  have hlo : |log ‖p.value z‖| ≤ B+log (1+‖z‖) := by simpa [PickSum.power] using (hlog z hz).1
  have hlogz : ‖Complex.log (p.value z)‖ ≤ B+π+log (2+‖z‖) := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    rw [Complex.log_re,Complex.log_im]
    linarith [Complex.abs_arg_le_pi (p.value z),log_le_log (by positivity : 0<1+‖z‖) (by linarith : 1+‖z‖≤2+‖z‖)]
  have hlog0 := log_nonneg (show 1≤2+‖z‖ by linarith [norm_nonneg z])
  have hs : ‖((1+t:ℝ):ℂ)‖ ≤ 2 := by rw [Complex.norm_of_nonneg (by linarith [ht.1])]; linarith [ht.2]
  have hx := mul_le_mul hs hlogz (norm_nonneg _) (by norm_num)
  have hb := norm_add_le (1:ℂ) (((1+t:ℝ):ℂ)*Complex.log (p.value z))
  rw [norm_one,norm_mul] at hb
  rw [PickSum.parameterSlope,norm_mul]
  calc
    _ ≤ M*((1+2*(B+π)+2)*(1+log (2+‖z‖))) := mul_le_mul hp (by
      nlinarith [mul_nonneg (show 0≤1+2*(B+π) by positivity) hlog0]) (norm_nonneg _) hM.le
    _ = _ := by ring

theorem PickSum.parameterFactor_sub_one {n : ℕ} (p : PickSum n) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ z : ℂ, 0≤z.im →
      ‖p.parameterFactor t z-1‖ ≤ t*(C*(1+log (2+‖z‖))) := by
  obtain ⟨C,hC,hbound⟩ := p.parameterSlope_bound
  refine ⟨C,hC,?_⟩
  intro t ht z hz
  have h := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (f:=fun s => p.parameterFactor s z) (fun s _ => (p.parameterFactor_hasDerivAt s hz).differentiableAt)
    (fun s hs => by rw [(p.parameterFactor_hasDerivAt s hz).deriv]; exact hbound s hs z hz)
    (show (0:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num) ht
  simpa [PickSum.parameterFactor,PickSum.power,Real.norm_eq_abs,abs_of_nonneg ht.1,mul_comm] using h

def PickSum.frozenError {n : ℕ} (p : PickSum n) (t : ℝ) (z : ℂ) : ℂ :=
  p.frozenLogSource t z-conj (dbar (logInput (p.power (1+t))) z)

def PickSum.frozenErrorSlope {n : ℕ} (p : PickSum n) (t : ℝ) (z : ℂ) : ℂ :=
  conj (p.parameterSlope t z)*(dbar (logInput p.value) z-conj (dbar (logInput p.value) z))

theorem PickSum.frozenError_factor {n : ℕ} (p : PickSum n) (t : ℝ) {z : ℂ} (hz : 0≤z.im) :
    p.frozenError t z = conj (p.parameterFactor t z)*
      (dbar (logInput p.value) z-conj (dbar (logInput p.value) z)) := by
  obtain ⟨ha,hb⟩ := p.critical_source_identity t hz
  simp [PickSum.frozenError,PickSum.parameterFactor,ha,hb,mul_sub,mul_assoc]

theorem PickSum.frozenError_hasDerivAt {n : ℕ} (p : PickSum n) (t : ℝ) {z : ℂ} (hz : 0≤z.im) :
    HasDerivAt (fun s => p.frozenError s z) (p.frozenErrorSlope t z) t := by
  have hc : HasDerivAt (fun s => conj (p.parameterFactor s z)) (conj (p.parameterSlope t z)) t :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (p.parameterFactor_hasDerivAt t hz)
  simpa only [PickSum.frozenErrorSlope,PickSum.frozenError_factor p _ hz] using
    hc.mul_const (dbar (logInput p.value) z-conj (dbar (logInput p.value) z))

theorem PickSum.frozenErrorSlope_bound {n : ℕ} (p : PickSum n) :
    ∃ C > 0, ∀ t ∈ Icc (0:ℝ) 1, ∀ z : ℂ, 0≤z.im →
      ‖p.frozenErrorSlope t z‖ ≤ C*(1+log (2+‖z‖))/(1+‖z‖)^4 := by
  obtain ⟨K,hK,hs⟩ := p.parameterSlope_bound
  obtain ⟨D,hD,hd⟩ := p.logSource_conjugation_defect
  refine ⟨K*D,by positivity,?_⟩
  intro t ht z hz
  rw [PickSum.frozenErrorSlope,norm_mul,Complex.norm_conj]
  have hlog := log_nonneg (show 1≤2+‖z‖ by linarith [norm_nonneg z])
  calc
    _ ≤ (K*(1+log (2+‖z‖)))*(D/(1+‖z‖)^4) := mul_le_mul (hs t ht z hz) (hd z hz) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Liu
