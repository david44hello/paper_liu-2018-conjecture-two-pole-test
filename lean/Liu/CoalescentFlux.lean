module

public import Liu.CoalescentFactors

@[expose] public section

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu.PickChart

/-- Equality of values and complex derivatives at the coalescent parameter. -/
def sameFirstOrder (f g : ℂ → ℂ) : Prop :=
  f 0=g 0 ∧ ∃ d, HasDerivAt f d 0 ∧ HasDerivAt g d 0

private theorem sameFirstOrder.mul {f g u v : ℂ → ℂ} (h : sameFirstOrder f g) (k : sameFirstOrder u v) :
    sameFirstOrder (fun w => f w*u w) (fun w => g w*v w) := by
  obtain ⟨he,d,hf,hg⟩ := h
  obtain ⟨ke,e,hu,hv⟩ := k
  exact ⟨by simp only [he,ke],_,hf.mul hu,by simpa only [←he,←ke] using hg.fun_mul hv⟩

private theorem sameFirstOrder.sub {f g u v : ℂ → ℂ} (h : sameFirstOrder f g) (k : sameFirstOrder u v) :
    sameFirstOrder (fun w => f w-u w) (fun w => g w-v w) := by
  obtain ⟨he,d,hf,hg⟩ := h
  obtain ⟨ke,e,hu,hv⟩ := k
  exact ⟨by simp only [he,ke],_,hf.sub hu,hg.sub hv⟩

private theorem sameFirstOrder.reflect {f g : ℂ → ℂ} (h : sameFirstOrder f g) :
    sameFirstOrder (fun w => conj (f (conj w))) (fun w => conj (g (conj w))) := by
  obtain ⟨he,d,hf,hg⟩ := h
  exact ⟨by simpa only [map_zero,he],conj d,by simpa only [map_zero,Function.comp_def] using hf.conj_conj,
    by simpa only [map_zero,Function.comp_def] using hg.conj_conj⟩

private theorem sameFirstOrder.const_mul {f g : ℂ → ℂ} (h : sameFirstOrder f g) (k : ℂ) :
    sameFirstOrder (fun w => k*f w) (fun w => k*g w) := by
  obtain ⟨he,d,hf,hg⟩ := h
  exact ⟨by simp only [he],_,hf.const_mul k,hg.const_mul k⟩

private theorem sameFirstOrder.div_const {f g : ℂ → ℂ} (h : sameFirstOrder f g) (k : ℂ) :
    sameFirstOrder (fun w => f w/k) (fun w => g w/k) := by
  obtain ⟨he,d,hf,hg⟩ := h
  exact ⟨by simp only [he],_,hf.div_const k,hg.div_const k⟩

private theorem sameFirstOrder.deriv_eq {f g : ℂ → ℂ} (h : sameFirstOrder f g) : deriv f 0=deriv g 0 := by
  obtain ⟨_,d,hf,hg⟩ := h
  rw [hf.deriv,hg.deriv]

/-- Pointwise equality through first order passes through both dominated integrals. -/
theorem flux_sameFirstOrder {P Q : PickChart} {U V : Set ℂ}
    (hP : P.Regular U) (hQ : Q.Regular V) (hU : (0:ℂ)∈U) (hV : (0:ℂ)∈V)
    (h : ∀ z : ℂ, 0≤z.im →
      sameFirstOrder (fun w => P.valueFactor w z) (fun w => Q.valueFactor w z) ∧
      sameFirstOrder (fun w => P.derivativeRatio w z) (fun w => Q.derivativeRatio w z)) :
    sameFirstOrder P.fluxExtension Q.fluxExtension := by
  have hh (z : ℂ) (hz : 0≤z.im) : sameFirstOrder (fun w => P.rho w z) (fun w => Q.rho w z) :=
    ((h z hz).1.mul (h z hz).2.reflect).div_const _
  have ht (x : ℝ) : sameFirstOrder (fun w => P.trace w x) (fun w => Q.trace w x) := by
    have hd := hP.trace_hasDeriv hU x
    have he := hQ.trace_hasDeriv hV x
    refine ⟨?_,_,hd,?_⟩
    · apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
      exact congrArg (_ * ·) (hh z (le_of_lt hz)).1
    · convert he using 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
      exact ((hh z (le_of_lt hz)).const_mul _).deriv_eq
  have hS (x : ℝ) : sameFirstOrder (fun w => P.value w x) (fun w => Q.value w x) := by
    simpa only [value,neg_one_mul] using (((h (x:ℂ) (by simp)).1.const_mul (-1)).div_const ((x:ℂ)+Complex.I))
  have hi (x : ℝ) : sameFirstOrder (fun w => P.fluxIntegrand w x) (fun w => Q.fluxIntegrand w x) :=
    ((ht x).mul (ht x).reflect).sub (((hS x).const_mul (k₀:ℂ)).mul (hS x).reflect)
  refine ⟨?_,_,hP.flux_hasDeriv hU,?_⟩
  · unfold fluxExtension
    rw [integral_congr_ae (Eventually.of_forall fun x => (hi x).1)]
  · convert hQ.flux_hasDeriv hV using 1
    rw [integral_congr_ae (Eventually.of_forall fun x => (hi x).deriv_eq)]

theorem moving_flux_first_order {a p l r : ℂ} (hp : p.im < 0) :
    let v := velocity a l r
    sameFirstOrder (moving a p l r).fluxExtension (moving a p v v).fluxExtension := by
  let v := velocity a l r
  have hv : velocity a v v = v := by unfold velocity; ring
  apply flux_sameFirstOrder (moving_regular ..) (moving_regular ..) (moving_origin hp) (moving_origin hp)
  intro z hz
  obtain ⟨f₀,g₀,hf,hg⟩ := moving_factors (a:=a) (l:=l) (r:=r) hp hz
  obtain ⟨F₀,G₀,hF,hG⟩ := moving_factors (a:=a) (l:=v) (r:=v) hp hz
  change HasDerivAt _ (velocity a v v/(z+Complex.I)/(nodeFactor p z)^2) 0 at hF hG
  rw [hv] at hF hG
  exact ⟨⟨f₀.trans F₀.symm,_,hf,hF⟩,⟨g₀.trans G₀.symm,_,hg,hG⟩⟩

end Liu.PickChart
