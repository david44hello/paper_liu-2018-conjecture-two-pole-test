import Liu.FirstOrderMajorant
import Liu.LinearPairing

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped Topology ComplexConjugate
namespace Liu

def mixedPoleIntegral (p q : ℂ) (R : ℝ) :=
  let A := pole 1 p
  let B := pole 1 q
  ∫ z in halfDisc R, ((k₀:ℂ)*A z*conj (B z)-field A z*conj (field B z)).re ∂area

def smallMassFirstOrder (p q : ℂ) :=
  let A := pole 1 p
  let B := pole 1 q
  2*limUnder atTop (mixedPoleIntegral p q) -
    2*(∫ z, field A z*conj (linearBlend (A z) (B z)) ∂upperArea).re

def lowerPolePick (p : ℂ) (hp : p.im<0) := singlePick 1 p.re (-p.im) zero_lt_one (neg_pos.mpr hp)

theorem lowerPolePick_value (p : ℂ) (hp : p.im<0) : (lowerPolePick p hp).value=pole 1 p := by
  rw [lowerPolePick,singlePick_value]; congr 1; apply Complex.ext <;> simp

theorem field_eq_witness_product {S : ℂ → ℂ} {z : ℂ} (hn : S z≠0) :
    field S z=S z*(((S z).arg:ℂ)-optimalWitness S z) := by
  unfold optimalWitness; field_simp [hn]; ring

/-- Lemma C.1, including existence of the mixed radial cutoff limit and
absolute convergence of the integral defining the first-order correction. -/
theorem smallMassFirstOrder_formula {q : ℂ} (hq : q.im<0) :
    let p := -Complex.I
    let Y := firstOrderIntegrand p q
    let J := mixedPoleIntegral p q
    Integrable Y upperArea ∧ Tendsto J atTop (𝓝 (limUnder atTop J)) ∧
    smallMassFirstOrder p q=2*singleConstant+2*(∫ z, Y z ∂upperArea).re ∧
    |smallMassFirstOrder p q-2*singleConstant|≤167 := by
  let p := -Complex.I
  have hp : p.im<0 := by simp [p]
  let A := pole 1 p
  let B := pole 1 q
  let Wa := optimalWitness A
  let Wb := optimalWitness B
  let L := fun z => field A z*conj (linearBlend (A z) (B z))
  let O := fun z => field A z*conj (B z*(Wa z-Wb z))
  let Y := firstOrderIntegrand p q
  let f := fun z => (Y z).re+(L z).re-(O z).re
  have hvA : (lowerPolePick p hp).value=A := lowerPolePick_value .. 
  have hvB : (lowerPolePick q hq).value=B := lowerPolePick_value .. 
  have hWa : isWitness Wa := by simpa only [Wa,←hvA] using (lowerPolePick p hp).optimalWitness_isWitness
  have hWb : isWitness Wb := by simpa only [Wb,←hvB] using (lowerPolePick q hq).optimalWitness_isWitness
  have ho := cross_witness_orthogonality (lowerPolePick p hp) (lowerPolePick q hq) hWa hWb
  dsimp only at ho; rw [hvA,hvB] at ho
  change Integrable O upperArea ∧ (∫ z, O z ∂upperArea)=0 at ho
  have hL : Integrable L upperArea := linearPairing_integrable hp hq
  obtain ⟨hY,hbound⟩ := firstOrderIntegral_bound hq
  change Integrable Y upperArea at hY
  change |(∫ z, Y z ∂upperArea).re|≤79 at hbound
  have hiY := Complex.reCLM.integrable_comp hY
  have hiL := Complex.reCLM.integrable_comp hL
  have hiO := Complex.reCLM.integrable_comp ho.1
  have hf : Integrable f upperArea := (hiY.add hiL).sub hiO
  have hv := (lowerPolePick p hp).finite_part.1
  rw [hvA] at hv
  have fe (R : ℝ) : mixedPoleIntegral p q R=truncatedDeficit A R+∫ z in halfDisc R, f z ∂area := by
    have hloc : IntegrableOn f (halfDisc R) area := (show IntegrableOn f upper area from hf).mono_set inter_subset_left
    have hd := (lowerPolePick p hp).deficit_local_integrable R
    rw [hvA] at hd
    rw [truncatedDeficit,←integral_add hd hloc]
    apply setIntegral_congr_fun (upper_open.measurableSet.inter isOpen_ball.measurableSet)
    intro z hz
    have hn {w : ℂ} (hw : w.im<0) : pole 1 w z≠0 := fun e => by
      have h := pole_im_pos zero_lt_one hw (show 0≤z.im from le_of_lt hz.1); simp [e] at h
    let ι := ((A z).arg:ℂ)-Wa z
    have H := firstOrder_pointwise (B:=B z) (W₁:=Wa z) (W₂:=Wb z) (hA:=hn hp)
    dsimp only at H
    have h₁ : field A z=A z*ι := field_eq_witness_product (hn hp)
    have h₂ : field B z=B z*(((B z).arg:ℂ)-Wb z) := field_eq_witness_product (hn hq)
    change (_-(A z*ι)*conj (B z*(((B z).arg:ℂ)-Wb z))).re-((A z*ι)*conj (linearBlend (A z) (B z))).re = _ at H
    rw [←h₁,←h₂] at H
    have hsplit : (A z*conj (B z)*firstOrderQ ι).re =
        k₀*‖A z‖^2-‖field A z‖^2+(Y z).re := by
      have h : A z*conj (B z)*firstOrderQ ι = A z*conj (A z)*firstOrderQ ι+Y z := by
        change _ = _ + A z*conj (B z-A z)*firstOrderQ ι
        rw [map_sub]; ring
      rw [h,Complex.add_re,Complex.mul_conj',←Complex.ofReal_pow,Complex.re_ofReal_mul,h₁,norm_mul,mul_pow]
      simp only [firstOrderQ,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,zero_mul,mul_zero,sub_zero]; ring
    change ((k₀:ℂ)*A z*conj (B z)-field A z*conj (field B z)).re = k₀*‖A z‖^2-‖field A z‖^2+f z
    change _ -(L z).re=(A z*conj (B z)*firstOrderQ ι).re-(O z).re at H
    rw [hsplit] at H
    dsimp only [f]; linarith only [H]
  have hJ := ((finite_part_limit hv).add (halfDisc_integral_limit hf)).congr (fun R => (fe R).symm)
  have hk : deficit A=singleConstant := by simpa [A] using singlePole_deficit 1 p zero_lt_one hp
  have hInt : (∫ z, f z ∂upperArea)=(∫ z,Y z ∂upperArea).re+(∫ z,L z ∂upperArea).re := by
    dsimp only [f]
    erw [integral_sub (hiY.add hiL) hiO,integral_add hiY hiL,integral_re hY,integral_re hL,integral_re ho.1,ho.2]; simp
  have heq : smallMassFirstOrder p q=2*singleConstant+2*(∫ z,Y z ∂upperArea).re := by
    change 2*limUnder atTop (mixedPoleIntegral p q)-2*(∫ z,L z ∂upperArea).re=_
    rw [hJ.limUnder_eq,hk,hInt]; ring
  refine ⟨hY,show Tendsto (mixedPoleIntegral p q) atTop (𝓝 (limUnder atTop (mixedPoleIntegral p q))) by rwa [hJ.limUnder_eq],heq,?_⟩
  change |smallMassFirstOrder p q-2*singleConstant|≤167
  rw [heq,add_sub_cancel_left,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

end Liu
