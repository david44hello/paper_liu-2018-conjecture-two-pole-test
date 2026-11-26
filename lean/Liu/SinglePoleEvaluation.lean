import Liu.CapQuotient
import Liu.DifferentiatedGauss
import Liu.SinglePoleDigits
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology
namespace Liu

theorem singleConstant_zeta_three : (singleConstant:ℂ)=(3/4:ℂ)*riemannZeta 3 := by
  rw [show riemannZeta 3=∑' n : ℕ, 1/(n:ℂ)^3 by simpa using zeta_nat_eq_tsum_of_gt_one (k:=3) (by decide)]
  simp [singleConstant,Complex.ofReal_tsum]

/-- The exact formula of Lemma A.2 for the actual half-plane projection quotient. -/
theorem cap_quotient_exact {α : ℝ} (ha : 1<α) (hb : α<2) :
    quotient (capPower α)=capExpression α := by
  have ht : 2-α∈Ioo (0:ℝ) 1 := by constructor <;> linarith
  have H := projected_gauss_sum ht
  rw [show 2-(2-α)=α by ring,show 2-2*(2-α)=2*α-2 by ring] at H
  have hN : 0<capNorm α := div_pos (Gamma_pos_of_pos (by linarith)) (sq_pos_of_pos (Gamma_pos_of_pos (by linarith)))
  have hG : discGamma (2-α) (2-α)=capNorm α := by
    dsimp [discGamma,capNorm]; rw [show 2-(2-α)-(2-α)=2*α-2 by ring,show 2-(2-α)=α by ring,←sq]
  have hV : gaussValue (2-α) 2=capNorm α := by
    dsimp [gaussValue,capNorm]; rw [show 2-2*(2-α)=2*α-2 by ring,show 2-(2-α)=α by ring]
  rw [cap_quotient_projection_series ha hb,H,hV,hG,capExpression]
  field_simp [hN.ne']; ring

/-- The expansion and strict sign in Lemma A.2 at the positive endpoint. -/
theorem cap_quotient_expansion :
    (∃ C ≥ 0, ∀ᶠ t in 𝓝[>] (0:ℝ),
      |quotient (capPower (1+t))-k₀-(π^2/6-3/2*(∑' n : ℕ, 1/(n:ℝ)^3))*t|≤C*t^2) ∧
    -0.1581513<π^2/6-3/2*(∑' n : ℕ, 1/(n:ℝ)^3) ∧
      π^2/6-3/2*(∑' n : ℕ, 1/(n:ℝ)^3)< -0.1581512 := by
  have hcoeff : π^2/6-3/2*(∑' n : ℕ, 1/(n:ℝ)^3)=2*k₀-2*singleConstant := by dsimp [k₀,singleConstant]; ring
  rw [hcoeff]
  refine ⟨?_,single_pole_decimal_bounds.2.2.2.2⟩
  obtain ⟨C,hC,h⟩ := capExpression_expansion
  refine ⟨C,hC,?_⟩
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  filter_upwards [h,self_mem_nhdsWithin (s:=Ioi 0) (a:=(0:ℝ)),hid.eventually_lt_const zero_lt_one] with t hh hp h1
  simpa only [cap_quotient_exact (by linarith [show 0<t from hp] : 1<1+t) (by linarith : 1+t<2)] using hh

theorem singlePole_deficit : coincidentDeficit := by
  apply coincidentDeficit_of_exact_cap_quotient
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin (s:=Ioi 0) (a:=(0:ℝ)),hid.eventually_lt_const zero_lt_one] with t hp ht
  exact cap_quotient_exact (by linarith [show 0<t from hp]) (by linarith)

/-- Corollary 3.4, for every positive mass and every strictly lower pole. -/
theorem singlePole_deficit_and_margin {a : ℝ} {w : ℂ} (ha : 0<a) (hw : w.im<0) :
    deficit (pole a w)=singleConstant*a^2 ∧
      deficit (pole a w)/a^2-k₀=singleConstant-k₀ ∧
      0.0790756<deficit (pole a w)/a^2-k₀ ∧ deficit (pole a w)/a^2-k₀<0.0790757 := by
  have H := singlePole_deficit a w ha hw
  rw [H,mul_div_cancel_right₀ _ (pow_ne_zero 2 ha.ne')]
  exact ⟨rfl,rfl,single_pole_decimal_bounds.2.2.1,single_pole_decimal_bounds.2.2.2.1⟩

theorem pair_deficit_of_five_inputs (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) (hsmall : smallMassDeficit) :
    k₀*p.mass^2 < deficit p.value := pair_deficit_of_six_inputs p hbox hflux h54 hE4 singlePole_deficit hsmall

theorem two_pole_test_of_five_inputs (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) (hsmall : smallMassDeficit) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2 < deficit p.value ∧ p.slope < 0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → p.quotientDomain ε ∧ quotient (critical p ε) < k₀ :=
  two_pole_test_of_six_inputs p hbox hflux h54 hE4 singlePole_deficit hsmall

end Liu
