module

public import Liu.Dilation

@[expose] public section

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace Liu

def verticalReflection : ℂ ≃ₗᵢ[ℝ] ℂ := Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)

private theorem reflection_apply (z : ℂ) : verticalReflection z = -conj z := rfl

def reflectFunction (S : ℂ → ℂ) : ℂ → ℂ := verticalReflection ∘ S ∘ verticalReflection

theorem reflect_deriv (S : ℂ → ℂ) (z : ℂ) :
    deriv (reflectFunction S) z = conj (deriv S (verticalReflection z)) := by
  have h : reflectFunction S = fun w => -((conj ∘ S ∘ conj) (-w)) := by
    funext w; simp [reflectFunction,reflection_apply]
  rw [h]
  change deriv (-(fun w => (conj ∘ S ∘ conj) (-w))) z = _
  rw [deriv.neg,deriv_comp_neg,deriv_conj_conj]
  simp [reflection_apply]

theorem reflect_source (S : ℂ → ℂ) (z : ℂ) :
    source (reflectFunction S) z = verticalReflection (source S (verticalReflection z)) := by
  unfold source
  rw [reflect_deriv]
  simp only [reflectFunction,Function.comp_apply,reflection_apply,map_neg,
    map_div₀,map_mul,Complex.conj_conj,Complex.conj_I,map_ofNat,neg_div_neg_eq]
  ring

private theorem reflection_area : MeasurePreserving verticalReflection area area := by
  have h := verticalReflection.measurePreserving
  exact ⟨h.measurable,by unfold area; rw [Measure.map_smul _ h.measurable.aemeasurable,h.map_eq]⟩

private theorem reflected_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) {s : Set ℂ} (hs : verticalReflection ⁻¹' s = s) :
    (∫ w in s, f (verticalReflection w) ∂area) = ∫ w in s, f w ∂area := by
  have h := reflection_area.setIntegral_preimage_emb verticalReflection.toHomeomorph.measurableEmbedding f s
  rwa [hs] at h

private theorem reflect_upper : verticalReflection ⁻¹' upper = upper := by ext z; simp [upper,reflection_apply]

theorem greenLog_verticalReflection (z w : ℂ) :
    greenLog (verticalReflection z) (verticalReflection w) = greenLog z w := by
  have hn (u v : ℂ) : ‖verticalReflection u - verticalReflection v‖ = ‖u-v‖ := by
    rw [←map_sub,LinearIsometryEquiv.norm_map]
  have hc : conj (verticalReflection w) = verticalReflection (conj w) := by simp [reflection_apply]
  simp only [greenLog,hc,hn]

theorem potential_verticalReflection (S : ℂ → ℂ) :
    potential (reflectFunction S) = reflectFunction (potential S) := by
  funext z
  let F := fun w : ℂ => (greenLog (verticalReflection z) w:ℂ)*source S w
  have hv (w : ℂ) : greenLog (verticalReflection z) (verticalReflection w) = greenLog z w :=
    greenLog_verticalReflection z w
  have h := reflected_integral (fun w => -conj (F w)) reflect_upper
  simp only [integral_neg,integral_conj] at h
  change (∫ w in upper, (greenLog z w:ℂ)*source (reflectFunction S) w ∂area) = -conj (∫ w in upper, F w ∂area)
  rw [←h,←integral_conj,←integral_neg]
  apply integral_congr_ae
  filter_upwards with w
  rw [reflect_source]
  dsimp only [F]
  rw [hv]
  simp [reflection_apply]

theorem field_verticalReflection (S : ℂ → ℂ) (z : ℂ) :
    field (reflectFunction S) z = conj (field S (verticalReflection z)) := by
  let J := verticalReflection.toContinuousLinearEquiv
  have h := J.comp_fderiv (f:=potential S ∘ J) (x:=z)
  rw [J.comp_right_fderiv] at h
  simp only [field,potential_verticalReflection]
  change -(fderiv ℝ (J ∘ (potential S ∘ J)) z 1 - Complex.I*fderiv ℝ (J ∘ (potential S ∘ J)) z Complex.I) = _
  rw [h]
  simp [J,ContinuousLinearMap.comp_apply,reflection_apply,Complex.conj_I]; ring

theorem truncatedDeficit_reflect (S : ℂ → ℂ) (R : ℝ) :
    truncatedDeficit (reflectFunction S) R = truncatedDeficit S R := by
  have hs : verticalReflection ⁻¹' halfDisc R = halfDisc R := by
    ext z; simp [halfDisc,upper,Metric.mem_ball,reflection_apply]
  have h := reflected_integral (fun z => k₀*‖S z‖^2-‖field S z‖^2) hs
  unfold truncatedDeficit
  simp_rw [field_verticalReflection]
  simpa only [reflectFunction,Function.comp_apply,
    LinearIsometryEquiv.norm_map,Complex.norm_conj] using h

theorem Pair.truncated_reflect (p : Pair) (f : Bool) (R : ℝ) :
    truncatedDeficit (p.reflect f).value R = truncatedDeficit p.value R := by
  cases f
  · rfl
  have h : (p.reflect true).value = reflectFunction p.value := by
    funext z
    have hp (a : ℝ) (w : ℂ) : pole a (verticalReflection w) z =
        verticalReflection (pole a w (verticalReflection z)) := by
      have hh : verticalReflection z-w = verticalReflection (z-verticalReflection w) := by
        simp [reflection_apply]; ring
      simp only [pole,hh,reflection_apply,map_div₀,map_neg,Complex.conj_ofReal,Complex.conj_conj,map_sub]
      rw [show -z-conj w = -(z+conj w) by ring]
      simp only [div_eq_mul_inv,inv_neg,neg_neg,sub_neg_eq_add,mul_neg,neg_mul] <;> ring
    change pole p.a₁ (verticalReflection p.w₁) z + pole p.a₂ (verticalReflection p.w₂) z =
      verticalReflection (pole p.a₁ p.w₁ (verticalReflection z)+pole p.a₂ p.w₂ (verticalReflection z))
    rw [map_add,hp,hp]
  rw [h,truncatedDeficit_reflect]

theorem Pair.reflect_deficit (p : Pair) (f : Bool) : deficit (p.reflect f).value = deficit p.value := by
  unfold deficit
  rw [show truncatedDeficit (p.reflect f).value = truncatedDeficit p.value from funext (p.truncated_reflect f)]

end Liu
