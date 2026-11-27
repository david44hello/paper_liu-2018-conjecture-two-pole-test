module

public import Liu.FrozenSource

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace Liu

def PickSum.frozenLogSource {n : ℕ} (p : PickSum n) (ε : ℝ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(p.value z/conj (p.value z))*conj (deriv (p.power (1+ε)) z)

theorem PickSum.critical_source_identity {n : ℕ} (p : PickSum n) (ε : ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    dbar (logInput (p.power (1+ε))) z =
      ((1+ε:ℝ):ℂ)*p.power ε z*dbar (logInput p.value) z ∧
    p.frozenLogSource ε z =
      ((1+ε:ℝ):ℂ)*conj (p.power ε z)*dbar (logInput p.value) z := by
  have hn : p.value z ≠ 0 := fun he => by have h := p.value_im_pos hz; simp [he] at h
  have hc : conj (p.power ε z) ≠ 0 := by simpa using p.power_nonzero ε hz
  have hvc : conj (p.value z) ≠ 0 := by simpa using hn
  have hp : p.power (1+ε) z = p.value z * p.power ε z := by
    unfold PickSum.power
    rw [Complex.ofReal_add,Complex.ofReal_one,Complex.cpow_add _ _ hn,Complex.cpow_one]
  rw [dbar_logInput (p.power_hasDerivAt ε hz) (p.power_nonzero (1+ε) hz),
    dbar_logInput (p.hasDerivAt hz).differentiableAt.hasDerivAt hn]
  unfold PickSum.frozenLogSource
  rw [(p.power_hasDerivAt ε hz).deriv,hp]
  simp only [map_mul,Complex.conj_ofReal]
  constructor
  · field_simp [hc,hvc]
  · ring

/-- Uniform fourth-order decay of the actual difference between the frozen source
and the conjugate of the logarithmic residual source in Appendix B, Step 2. -/
theorem PickSum.frozen_source_error {n : ℕ} (p : PickSum n) :
    ∃ C > 0, ∀ ε ∈ Set.Icc (0:ℝ) 1, ∀ z : ℂ, 0 ≤ z.im →
      ‖p.frozenLogSource ε z-conj (dbar (logInput (p.power (1+ε))) z)‖ ≤ C/(1+‖z‖)^4 := by
  obtain ⟨K,hK,h⟩ := p.logSource_conjugation_defect
  let M := max 1 p.bound
  have hM : 1≤M := le_max_left ..
  have hp : 0<M := zero_lt_one.trans_le hM
  refine ⟨2*M*K,by positivity,?_⟩
  intro ε he z hz
  have hs := p.critical_source_identity ε hz
  rw [hs.1,hs.2]
  simp only [map_mul,Complex.conj_ofReal,←mul_sub]
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [he.1] : 0≤1+ε),
    Complex.norm_conj]
  have hv : ‖p.value z‖ ≤ M := (p.global_decay hz).trans
    ((div_le_self p.bound_pos.le (by linarith [norm_nonneg z])).trans (le_max_right ..))
  have hpwr : ‖p.power ε z‖ ≤ M := by
    change ‖(p.value z)^(ε:ℂ)‖ ≤ M
    rw [Complex.norm_cpow_real]
    calc
      _ ≤ M^ε := Real.rpow_le_rpow (norm_nonneg _) hv he.1
      _ ≤ M^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hM he.2
      _ = M := Real.rpow_one _
  calc
    _ ≤ (2*M)*(K/(1+‖z‖)^4) := mul_le_mul (mul_le_mul (by linarith [he.2]) hpwr (norm_nonneg _) (by norm_num))
      (h z hz) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Liu
