import Liu.CapHilbert

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate InnerProductSpace
namespace Liu

private theorem capFactor_nonzero (α : ℝ) : capFactor α≠0 := by
  have hn : (2:ℂ)*Complex.I≠0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  unfold capFactor; rw [Complex.cpow_def_of_ne_zero hn]; exact mul_ne_zero hn (Complex.exp_ne_zero _)

theorem capPower_energy {α : ℝ} (ha : 1<α) (hb : α<2) :
    MemLp (capPower α) 2 upperArea ∧ energy (capPower α)=‖capFactor α‖^2*capNorm α := by
  have hm : Measurable (capPower α) := by unfold capPower; fun_prop
  have hL : MemLp (capPower α) 2 upperArea := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    apply (cayleyPull_normSq_integrable_iff (show Complex.I∈upper by simp [upper]) _).mpr
    have hd := discPower_memLp (a:=2-α) (by linarith) (by linarith)
    have hi := ((memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd).const_mul (‖capFactor α‖^2)
    exact hi.congr ((ae_restrict_mem (μ:=area) (Metric.isOpen_ball.measurableSet : MeasurableSet disc)).mono fun w hw =>
      by dsimp only; rw [cap_cayley_pull α hw,norm_mul,mul_pow])
  refine ⟨hL,?_⟩
  rw [energy_eq_integral hL,upperArea,cayley_area_integral (show Complex.I∈upper by simp [upper]),
    ←discPower_energy ha hb,←integral_const_mul]
  apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
  intro w hw
  have hh := congrArg (fun z : ℂ => ‖z‖^2) (cap_cayley_pull α hw)
  simpa only [cayleyPull,norm_mul,mul_pow,smul_eq_mul,mul_comm ‖cayleyJac Complex.I w‖,mul_comm (‖cayleyJac Complex.I w‖^2)] using hh

private def capHolPart (α : ℝ) (z : ℂ) := capPower α z*((α:ℂ)/2*discLog (cayleyInv Complex.I z)-(α*log 2:ℝ))

private theorem cap_log_split (α : ℝ) {z : ℂ} (hz : z∈upper) :
    logInput (capPower α) z=(α:ℂ)/2*capAntiInput α z+capHolPart α z := by
  obtain ⟨hw,he⟩ := cayley_inv_right (show Complex.I∈upper by simp [upper]) hz
  have hh := cap_cayley_log_norm α hw
  rw [he] at hh
  dsimp only [capHolPart,capAntiInput,logInput]
  rw [hh]; push_cast
  have h := Complex.add_conj (discLog (cayleyInv Complex.I z))
  push_cast at h
  linear_combination (norm := ring) -(capPower α z*(α:ℂ)/2)*h

private theorem capHolPart_analytic (α : ℝ) : DifferentiableOn ℂ (capHolPart α) upper := by
  intro z hz
  have hi : 0<(z+Complex.I).im := by simp; linarith [show 0<z.im from hz]
  have hn : z-conj Complex.I≠0 := fun he => by rw [Complex.conj_I,sub_neg_eq_add] at he; rw [he] at hi; exact (lt_irrefl _ hi)
  have hs : z+Complex.I∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr hi.ne')
  have hc : ‖cayleyInv Complex.I z‖<1 := (cayley_inv_right (show Complex.I∈upper by simp [upper]) hz).1 |> fun h => by simpa [disc] using h
  have hl : 1-cayleyInv Complex.I z∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [Complex.re_le_norm (cayleyInv Complex.I z)]))
  have hf : DifferentiableAt ℂ (capPower α) z := by unfold capPower; fun_prop (disch := assumption)
  have hd : DifferentiableAt ℂ (cayleyInv Complex.I) z := by unfold cayleyInv; fun_prop (disch := assumption)
  exact (hf.mul ((((hd.const_sub 1).clog hl).const_mul ((α:ℂ)/2)).sub_const ((α*log 2:ℝ):ℂ))).differentiableWithinAt

private theorem capHolPart_memLp {α : ℝ} (ha : 1<α) (hb : α<2) : MemLp (capHolPart α) 2 upperArea := by
  have h := (capPower_energy ha hb).1
  have hv := capAntiInput_memLp ha hb
  have hs := hv.const_smul ((α:ℂ)/2)
  have hc := h.const_smul ((α*log 2:ℝ):ℂ)
  have ht : MemLp (fun z => capPower α z*discLog (cayleyInv Complex.I z)) 2 upperArea := hv.congr_norm
    (by unfold capPower discLog cayleyInv; fun_prop) (ae_of_all _ fun _ => by simp [capAntiInput])
  apply ((ht.const_smul ((α:ℂ)/2)).sub hc).ae_eq
  filter_upwards with z
  dsimp only [capHolPart,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]; ring

/-- Appendix A.2 before evaluating the remaining scalar series. The numerator
uses the actual Hilbert projection and the denominator is the printed N_alpha. -/
theorem cap_quotient_projection_series {α : ℝ} (ha : 1<α) (hb : α<2) :
    quotient (capPower α)=α^2/4*(discGamma (2-α) (2-α)*(trigamma (2*α-2)+(psi α-psi (2*α-2))^2)-
      (∑' m : ℕ, (capCoeff (2-α) m)^2/((m:ℝ)+1)*(psi α-psi ((m:ℝ)+2))^2))/capNorm α := by
  letI : analyticSubspace.HasOrthogonalProjection := by unfold analyticSubspace; infer_instance
  let H := capAntiInput α
  let V := capHolPart α
  let F := capPower α
  let c : ℂ := (α:ℂ)/2
  have hH : MemLp H 2 upperArea := capAntiInput_memLp ha hb
  have hV : MemLp V 2 upperArea := capHolPart_memLp ha hb
  have hS : MemLp (c • H+V) 2 upperArea := (hH.const_smul c).add hV
  have hae : logInput F =ᵐ[upperArea] c • H+V := (ae_restrict_iff' upper_open.measurableSet).mpr (ae_of_all _ fun _ hz => cap_log_split α hz)
  have hF := (memLp_congr_ae hae).mpr hS
  have hsplit : asL2 (logInput F)=c • asL2 H+asL2 V := by
    rw [←asL2_smul c hH,←asL2_add (hH.const_smul c) hV]
    simp only [asL2,dif_pos hF,dif_pos hS]
    exact Lp.ext (hF.coeFn_toLp.trans (hae.trans hS.coeFn_toLp.symm))
  have hfix : project (asL2 V)=asL2 V := by
    simpa only [asL2,dif_pos hV] using project_fixes_analytic hV (capHolPart_analytic α)
  have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection (asL2 H) analyticSubspace
  rw [Submodule.starProjection_orthogonal_val] at hpy
  change ‖asL2 H‖^2 = ‖project (asL2 H)‖^2 + ‖asL2 H-project (asL2 H)‖^2 at hpy
  have hp := (capAntiInput_projected_energy ha hb).tsum_eq
  let S := ∑' m : ℕ, (capCoeff (2-α) m)^2/((m:ℝ)+1)*(psi α-psi ((m:ℝ)+2))^2
  have hproj : ‖project (asL2 H)‖^2 = ‖capFactor α‖^2*S := by
    rw [←hp,←tsum_mul_left]
    apply tsum_congr; intro m; ring
  have hh := capAntiInput_energy ha hb
  change ‖asL2 H‖^2=_ at hh
  have den := (capPower_energy ha hb).2
  have hc : ‖c‖^2=α^2/4 := by dsimp [c]; rw [norm_div,Complex.norm_of_nonneg (by linarith),Complex.norm_two,div_pow]; norm_num
  unfold quotient
  change ‖asL2 (logInput F)-project (asL2 (logInput F))‖^2/energy F=_
  rw [hsplit,map_add,map_smul,hfix,add_sub_add_right_eq_sub,←smul_sub,norm_smul,mul_pow,hc,
    show ‖asL2 H-project (asL2 H)‖^2=‖asL2 H‖^2-‖project (asL2 H)‖^2 by linarith only [hpy],hh,hproj,den]
  dsimp only [S]; field_simp [norm_ne_zero_iff.mpr (capFactor_nonzero α)] <;> ring

end Liu
