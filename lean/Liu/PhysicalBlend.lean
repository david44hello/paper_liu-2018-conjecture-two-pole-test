module

public import Liu.SmallFirstOrder
public import Liu.BlendedWitness
public import Liu.MergedPoles

@[expose] public section

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped ComplexConjugate Topology
namespace Liu

/-- Exact density identity before taking any finite-part limits. -/
private theorem blend_energy_algebra (A B v₁ v₂ g l : ℂ) (m : ℝ) :
    k₀*‖A+(m:ℂ)*B‖^2-‖v₁+(m:ℂ)*v₂+g‖^2 =
    (k₀*‖A‖^2-‖v₁‖^2)+m^2*(k₀*‖B‖^2-‖v₂‖^2)+
    2*m*((k₀:ℂ)*A*conj B-v₁*conj v₂).re-2*m*(v₁*conj l).re-
    2*(v₁*conj (g-(m:ℂ)*l)).re-‖g‖^2-2*m*(v₂*conj g).re := by
  simp [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]; ring

private theorem blend_field_identity {A B W₁ W₂ : ℂ} (hA : A∈upper) (hB : B∈upper)
    {m : ℝ} (hm : 0 < m) :
    let S := A+(m:ℂ)*B
    let W := (A*W₁+((m:ℂ)*B)*W₂)/S
    S*((S.arg:ℂ)-W) =
      A*((A.arg:ℂ)-W₁)+(m:ℂ)*(B*((B.arg:ℂ)-W₂))+blendedError A ((m:ℂ)*B) := by
  have hB' : (m:ℂ)*B∈upper := by simpa [upper,Complex.mul_im] using mul_pos hm (show 0<B.im from hB)
  have hn : A+(m:ℂ)*B≠0 := fun e => by
    have h : 0<(A+(m:ℂ)*B).im := add_pos (show 0<A.im from hA) (show 0<((m:ℂ)*B).im from hB')
    simp [e] at h
  dsimp only
  rw [blendedError_identity hA hB',Complex.arg_real_mul _ hm]; field_simp [hn]; ring

def smallMassPair (q : ℂ) (m : ℝ) (hq : q.im<0) (hm : 0 < m) : Pair :=
  ⟨1,m,-Complex.I,q,zero_lt_one,hm,by simp,hq⟩

/-- Appendix C's blended finite part evaluated with the two physical fields. -/
theorem blended_deficit_lower {q : ℂ} (hq : q.im<0) {m : ℝ} (hm : 0 < m) (hm' : m≤1/10) :
    let p := -Complex.I
    singleConstant*(1+m^2)+m*smallMassFirstOrder p q+smallMassRemainder p q m ≤
      deficit (smallMassPair q m hq hm).value := by
  let p := -Complex.I
  have hp : p.im<0 := by simp [p]
  let A := pole 1 p
  let B := pole 1 q
  let E := smallMassPair q m hq hm
  let S := E.value
  let pa := lowerPolePick p hp
  let pb := lowerPolePick q hq
  let pm := singlePick m q.re (-q.im) hm (neg_pos.mpr hq)
  have ha : pa.value=A := lowerPolePick_value ..
  have hb : pb.value=B := lowerPolePick_value ..
  have heq : (q.re:ℂ)-((-q.im:ℝ):ℂ)*Complex.I=q := by apply Complex.ext <;> simp
  have hb' : pm.value=fun z => (m:ℂ)*B z := by
    rw [singlePick_value,heq]; funext z; simp [B,pole]; ring
  have hSv (z : ℂ) : S z=A z+(m:ℂ)*B z := by dsimp [S,E,smallMassPair,Pair.value,A,B,pole,p]; push_cast; ring
  have he : E.toPick.value=S := by funext z; simp [S,Pair.toPick,PickSum.value,Pair.value,Fin.sum_univ_two]
  have hsum : E.toPick.value=pa.value+pm.value := by rw [he,ha,hb']; funext z; exact hSv z
  let W := blendWitness A pm.value (optimalWitness A) (optimalWitness B)
  have hWa := pa.optimalWitness_isWitness
  have hWb := pb.optimalWitness_isWitness
  rw [ha] at hWa; rw [hb] at hWb
  have hW : isWitness W := by simpa only [W,ha] using blendWitness_isWitness pa pm E.toPick hsum hWa hWb
  obtain ⟨_,_,_,hlo,_⟩ := E.toPick.witness_identity.2 W hW
  rw [he] at hlo
  let g := fun z => blendedError (A z) ((m:ℂ)*B z)
  let l := fun z => linearBlend (A z) (B z)
  let P := fun z => field A z*conj (g z-(m:ℂ)*l z)
  let L := fun z => field A z*conj (l z)
  let Q := fun z => field B z*conj (g z)
  let F := fun z => -(2*m)*(L z).re-2*(P z).re-‖g z‖^2-2*m*(Q z).re
  obtain ⟨hP,hQ,hg,_⟩ := smallMassRemainder_estimates hp hq hm hm'
  have hL := linearPairing_integrable hp hq
  change Integrable P upperArea at hP; change Integrable Q upperArea at hQ
  change Integrable L upperArea at hL; change Integrable (fun z => ‖g z‖^2) upperArea at hg
  have iL := Complex.reCLM.integrable_comp hL
  have iP := Complex.reCLM.integrable_comp hP
  have iQ := Complex.reCLM.integrable_comp hQ
  have hF : Integrable F upperArea := ((((iL.const_mul (-(2*m))).sub (iP.const_mul 2)).sub hg).sub (iQ.const_mul (2*m)))
  let M := fun z => ((k₀:ℂ)*A z*conj (B z)-field A z*conj (field B z)).re
  let DA := fun z => k₀*‖A z‖^2-‖field A z‖^2
  let DB := fun z => k₀*‖B z‖^2-‖field B z‖^2
  have hcut (R : ℝ) : truncatedWitness S W R =
      truncatedDeficit A R +m^2*truncatedDeficit B R+2*m*mixedPoleIntegral p q R+(∫ z in halfDisc R,F z ∂area) := by
    have iA : IntegrableOn DA (halfDisc R) area := by simpa only [DA,←ha] using pa.deficit_local_integrable R
    have iB : IntegrableOn DB (halfDisc R) area := by simpa only [DB,←hb] using pb.deficit_local_integrable R
    have iF := (show IntegrableOn F upper area from hF).mono_set (show halfDisc R⊆upper from inter_subset_left)
    have iM : IntegrableOn M (halfDisc R) area := by
      let U := {z : ℂ | 0≤z.im}
      have cA : ContinuousOn A U := by rw [←ha]; exact fun _ hz => (pa.hasDerivAt hz).continuousAt.continuousWithinAt
      have cB : ContinuousOn B U := by rw [←hb]; exact fun _ hz => (pb.hasDerivAt hz).continuousAt.continuousWithinAt
      have cFA := pa.field_continuous_closed; rw [ha] at cFA
      have cFB := pb.field_continuous_closed; rw [hb] at cFB
      have hc : ContinuousOn M U := Complex.continuous_re.comp_continuousOn
        (((continuousOn_const.mul cA).mul (Complex.continuous_conj.comp_continuousOn cB)).sub
        (cFA.mul (Complex.continuous_conj.comp_continuousOn cFB)))
      letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
      exact ((hc.mono inter_subset_left).integrableOn_compact ((isCompact_closedBall (0:ℂ) R).inter_left
        (isClosed_le continuous_const Complex.continuous_im))).mono_set fun z hz => ⟨(show 0<z.im from hz.1).le,ball_subset_closedBall hz.2⟩
    change _ = (∫ z in halfDisc R,DA z ∂area)+m^2*(∫ z in halfDisc R,DB z ∂area)+2*m*(∫ z in halfDisc R,M z ∂area)+_
    erw [←integral_const_mul,←integral_const_mul,←integral_add iA (iB.const_mul (m^2)),
      ←integral_add (iA.add (iB.const_mul (m^2))) (iM.const_mul (2*m)),
      ←integral_add ((iA.add (iB.const_mul (m^2))).add (iM.const_mul (2*m))) iF]
    apply setIntegral_congr_fun (upper_open.measurableSet.inter isOpen_ball.measurableSet)
    intro z hz
    have h₁ : A z∈upper := pole_im_pos zero_lt_one hp (le_of_lt hz.1)
    have h₂ : B z∈upper := pole_im_pos zero_lt_one hq (le_of_lt hz.1)
    have n₁ : A z≠0 := fun h => by simpa [upper,h] using h₁
    have n₂ : B z≠0 := fun h => by simpa [upper,h] using h₂
    have hfield : S z*(((S z).arg:ℂ)-W z)=field A z+(m:ℂ)*field B z+g z := by
      rw [field_eq_witness_product n₁,field_eq_witness_product n₂,hSv]
      dsimp only [W,blendWitness]; rw [hb']
      exact blend_field_identity (W₁:=optimalWitness A z) (W₂:=optimalWitness B z) h₁ h₂ hm
    dsimp only [Pi.add_apply,Pi.sub_apply,DA,DB,F,M,P,Q,L]
    rw [←mul_pow,←norm_mul,hfield,hSv]
    linarith only [blend_energy_algebra (A z) (B z) (field A z) (field B z) (g z) (l z) m]
  have hA := finite_part_limit pa.finite_part.1; rw [ha] at hA
  have hB := finite_part_limit pb.finite_part.1; rw [hb] at hB
  have hJ := (smallMassFirstOrder_formula hq).2.1
  have hlim := ((((hA.add (hB.const_mul (m^2))).add (hJ.const_mul (2*m))).add (halfDisc_integral_limit hF)).congr
    (fun R => (hcut R).symm))
  have hI : (∫ z,F z ∂upperArea)= -(2*m)*(∫ z,L z ∂upperArea).re+smallMassRemainder p q m := by
    dsimp only [F]
    erw [integral_sub (((iL.const_mul (-(2*m))).sub (iP.const_mul 2)).sub hg) (iQ.const_mul (2*m)),
      integral_sub ((iL.const_mul (-(2*m))).sub (iP.const_mul 2)) hg,integral_sub (iL.const_mul (-(2*m))) (iP.const_mul 2)]
    simp only [integral_const_mul]
    erw [integral_re hL,integral_re hP,integral_re hQ]
    change -(2*m)*(∫ z,L z ∂upperArea).re-2*(∫ z,P z ∂upperArea).re-(∫ z, ‖g z‖^2 ∂upperArea)-2*m*(∫ z,Q z ∂upperArea).re = _ + (-2*(∫ z,P z ∂upperArea).re-(∫ z,‖g z‖^2 ∂upperArea)-2*m*(∫ z,Q z ∂upperArea).re)
    ring
  rw [hlim.limUnder_eq,hI] at hlo
  have ha' : deficit A=singleConstant := by simpa [A] using singlePole_deficit 1 p zero_lt_one hp
  have hb'' : deficit B=singleConstant := by simpa [B] using singlePole_deficit 1 q zero_lt_one hq
  rw [ha',hb''] at hlo
  change _≤deficit S
  change singleConstant*(1+m^2)+m*(2*limUnder atTop (mixedPoleIntegral p q)-2*(∫ z,L z ∂upperArea).re)+_≤_
  linarith only [hlo]

end Liu
