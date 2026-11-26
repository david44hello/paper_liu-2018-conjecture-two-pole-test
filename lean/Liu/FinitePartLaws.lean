import Liu.RadialField
import Liu.TwoPoleReduction

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

theorem PickSum.finite_part_laws {n : ℕ} (p : PickSum n) :
    finitePartExists p.value ∧
    (∀ x : ℝ, finitePartExists (fun z => p.value (z-(x:ℂ))) ∧
      deficit (fun z => p.value (z-(x:ℂ)))=deficit p.value) ∧
    (∀ scale : ℝ, 0<scale → deficit (fun z => ((scale⁻¹:ℝ):ℂ)*p.value (z/(scale:ℂ))) = deficit p.value) ∧
    deficit (reflectFunction p.value) = deficit p.value ∧
    (∀ c : ℝ, deficit (fun z => (c:ℂ)*p.value z)=c^2*deficit p.value) := by
  have hf := p.finite_part.1
  refine ⟨hf,?_,?_,?_,deficit_mass_scale hf⟩
  · intro x
    simpa only [Complex.ofReal_neg,←sub_eq_add_neg] using
      shifted_finite_part p.bound_pos.le (fun w hw => p.global_decay (le_of_lt hw)) hf (-x)
  · intro scale hscale
    have he : (fun z => ((scale⁻¹:ℝ):ℂ)*p.value (z/(scale:ℂ))) = dilateFunction p.value scale⁻¹ := by
      funext w; simp [dilateFunction,Complex.real_smul,div_eq_mul_inv,mul_comm]
    exact he ▸ deficit_dilate hf (inv_pos.mpr hscale)
  · unfold deficit
    rw [show truncatedDeficit (reflectFunction p.value)=truncatedDeficit p.value from funext (truncatedDeficit_reflect _)]

theorem Pair.finite_part (p : Pair) : finitePartExists p.value := by
  have hv : p.toPick.value=p.value := by
    funext z; simp [PickSum.value,Pair.toPick,Pair.value,Fin.sum_univ_two]
  exact hv ▸ p.toPick.finite_part.1

/-- Six inputs remain for the deficit, with the actual finite part and all changes
of coordinates proved for every pair, including pairs with coincident poles. -/
theorem pair_deficit_of_six_inputs (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) (hcoinc : coincidentDeficit) (hsmall : smallMassDeficit) :
    k₀*p.mass^2 < deficit p.value :=
  pair_deficit_of_local_representation p hbox hflux h54 hE4 hcoinc hsmall (p.representation_of_finite_part p.finite_part)

theorem two_pole_test_of_seven_inputs (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) (hcoinc : coincidentDeficit) (hsmall : smallMassDeficit)
    (hnum : Tendsto (fun ε => residual (critical p ε)) (𝓝[>] 0) (𝓝 (k₀*p.mass^2-deficit p.value))) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2 < deficit p.value ∧ p.slope < 0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → p.quotientDomain ε ∧ quotient (critical p ε) < k₀ :=
  two_pole_test_of_finite_part p hbox hflux h54 hE4 hcoinc hsmall p.finite_part hnum

end Liu
