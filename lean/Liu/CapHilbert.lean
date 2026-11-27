module

public import Liu.CapProjection

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate InnerProductSpace
namespace Liu

/-- The part of the logarithmic cap input carrying the antiholomorphic logarithm. -/
def capAntiInput (α : ℝ) (z : ℂ) := capPower α z*conj (discLog (cayleyInv Complex.I z))

theorem capAntiInput_pull (α : ℝ) {w : ℂ} (hw : w∈disc) :
    cayleyPull Complex.I (capAntiInput α) w=capFactor α*(discPower (2-α) w*conj (discLog w)) := by
  have h := cap_cayley_pull α hw
  rw [cayleyPull,capAntiInput,(cayley_inv_left (show Complex.I∈upper by simp [upper]) hw).2]
  dsimp only [cayleyPull] at h; linear_combination (norm := ring) conj (discLog w)*h

theorem capAntiInput_memLp {α : ℝ} (ha : 1<α) (hb : α<2) : MemLp (capAntiInput α) 2 upperArea := by
  have hm : Measurable (capAntiInput α) := by unfold capAntiInput capPower discLog cayleyInv; fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (cayleyPull_normSq_integrable_iff (show Complex.I∈upper by simp [upper]) _).mpr
  let t := 2-α
  have ht : t∈Ioo (0:ℝ) 1 := by dsimp [t]; constructor <;> linarith
  obtain ⟨B,hB,hbound⟩ := disc_log_domination (show 2*t<2 by linarith [ht.2])
  have hmeas : Measurable (fun w => ‖cayleyPull Complex.I (capAntiInput α) w‖^2) := by
    unfold cayleyPull cayley cayleyJac; fun_prop
  apply (hB.const_mul (‖capFactor α‖^2)).mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ:=area) (Metric.isOpen_ball.measurableSet : MeasurableSet disc)] with w hw
  have hn : 1-w≠0 := fun he => by rw [←sub_eq_zero.mp he] at hw; simpa [disc] using hw
  have hr := norm_pos_iff.mpr hn
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),capAntiInput_pull α hw]
  simp only [norm_mul,mul_pow,Complex.norm_conj,discPower_norm]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  change (‖1-w‖^(-t))^2*‖discLog w‖^2 ≤ _
  rw [←rpow_ofNat (‖1-w‖^(-t)) 2,←rpow_mul hr.le,show -t*(2:ℝ)= -(2*t) by ring]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖discLog w‖≤1+‖discLog w‖) 2) (rpow_nonneg hr.le _)).trans
    (hbound w hw (2*t) ⟨by linarith [ht.1],le_rfl⟩)

private theorem upper_norm_integral_pull (f : ℂ → ℂ) :
    (∫ z, ‖f z‖^2 ∂upperArea)=∫ w in disc, ‖cayleyPull Complex.I f w‖^2 ∂area := by
  rw [upperArea,cayley_area_integral (show Complex.I∈upper by simp [upper])]
  apply integral_congr_ae; filter_upwards with w; simp [cayleyPull,mul_pow,mul_comm]

theorem capAntiInput_energy {α : ℝ} (ha : 1<α) (hb : α<2) :
    energy (capAntiInput α)=‖capFactor α‖^2*(discGamma (2-α) (2-α)*
      (trigamma (2*α-2)+(psi α-psi (2*α-2))^2)) := by
  rw [energy_eq_integral (capAntiInput_memLp ha hb),upper_norm_integral_pull]
  rw [setIntegral_congr_fun (s:=disc) Metric.isOpen_ball.measurableSet
    (g:=fun w => ‖capFactor α‖^2*‖discPower (2-α) w*conj (discLog w)‖^2)
    (fun w hw => by dsimp only; rw [capAntiInput_pull α hw,norm_mul,mul_pow]),integral_const_mul,
    discPower_log_energy (show 2-α∈Ioo (0:ℝ) 1 by constructor <;> linarith),
    show 2-(2-α)-(2-α)=2*α-2 by ring,show 2-(2-α)=α by ring]

/-- The actual projected norm as a convergent sum of the digamma moments. -/
theorem capAntiInput_projected_energy {α : ℝ} (ha : 1<α) (hb : α<2) :
    HasSum (fun m : ℕ => ‖capFactor α‖^2*(capCoeff (2-α) m)^2/((m:ℝ)+1)*(psi α-psi ((m:ℝ)+2))^2)
      (‖project (asL2 (capAntiInput α))‖^2) := by
  have hL := capAntiInput_memLp ha hb
  have ht : 2-α∈Ioo (0:ℝ) 1 := by constructor <;> linarith
  apply (project_norm_sq_series _).congr_fun
  intro m
  rw [asL2,dif_pos hL,upperUnitMonomial,inner_smul_left,Complex.conj_ofReal,upperMonomial_inner]
  have he := setIntegral_congr_fun (μ:=area) (s:=disc) Metric.isOpen_ball.measurableSet
    (f:=fun w => cayleyPull Complex.I (capAntiInput α) w*conj (w^m))
    (g:=fun w => capFactor α*(discPower (2-α) w*conj (discLog w)*conj (w^m)))
    (fun w hw => by dsimp only; rw [capAntiInput_pull α hw]; ring)
  rw [he,integral_const_mul,discPower_log_moment ht,show 2-(2-α)=α by ring]
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,Real.sq_sqrt (by positivity : 0≤(m:ℝ)+1)]
  field_simp

end Liu
