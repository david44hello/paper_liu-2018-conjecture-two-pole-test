module

public import Liu.RadialSource

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace Liu

/-- The physical Pick source is the actual Wirtinger derivative of S Arg S
throughout the closed upper half-plane. -/
theorem PickSum.argument_source_identity {n : ℕ} (p : PickSum n) {z : ℂ} (hz : 0≤z.im) :
    dbar (fun w => p.value w*(Complex.arg (p.value w):ℂ)) z = source p.value z := by
  let S := p.value
  have hp : S z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr (p.value_im_pos hz).ne')
  have hn : S z≠0 := Complex.slitPlane_ne_zero hp
  have df : HasDerivAt S (deriv S z) z := (p.hasDerivAt hz).differentiableAt.hasDerivAt
  have dl := (df.clog hp).complexToReal_fderiv
  have dc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z dl
  have d := (df.complexToReal_fderiv.mul (dl.sub dc)).mul_const (2*Complex.I)⁻¹
  let F := fun w => (S w*(Complex.log (S w)-conj (Complex.log (S w))))*(2*Complex.I)⁻¹
  have eqn : (fun w => p.value w*(Complex.arg (p.value w):ℂ)) = F := by
    funext w
    rw [←Complex.log_im,Complex.im_eq_sub_conj]
    dsimp [F,S]; ring
  change HasFDerivAt F _ z at d
  rw [eqn,dbar,d.fderiv]
  change _ = (Complex.I/2)*(S z/conj (S z))*conj (deriv S z)
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.one_apply,smul_eq_mul,Function.comp_apply,
    ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply,one_mul,mul_one,map_mul,map_div₀,Complex.conj_I]
  have hnc := (map_ne_zero (starRingEnd ℂ)).mpr hn
  field_simp [hn,hnc,Complex.I_ne_zero] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

end Liu
