import Liu.Normalize

noncomputable section
open Set
namespace Liu

def Pair.swap (p : Pair) : Pair := ⟨p.a₂,p.a₁,p.w₂,p.w₁,p.ha₂,p.ha₁,p.hw₂,p.hw₁⟩

theorem Pair.swap_value (p : Pair) : p.swap.value = p.value := by
  funext z
  simp [Pair.swap,Pair.value,add_comm]

def Pair.shift (p : Pair) (x : ℝ) : Pair :=
  { p with w₁ := p.w₁ - (x:ℂ), w₂ := p.w₂ - (x:ℂ),
           hw₁ := by simpa using p.hw₁, hw₂ := by simpa using p.hw₂ }

def Pair.reflect (p : Pair) (f : Bool) : Pair :=
  { p with w₁ := reflectIf f p.w₁, w₂ := reflectIf f p.w₂,
           hw₁ := by simpa [reflectIf_im] using p.hw₁, hw₂ := by simpa [reflectIf_im] using p.hw₂ }

def Pair.dilate (p : Pair) (d : ℝ) (hd : 0 < d) : Pair :=
  { p with w₁ := p.w₁ / (d:ℂ), w₂ := p.w₂ / (d:ℂ),
           hw₁ := by simpa [Complex.div_ofReal_im] using div_neg_of_neg_of_pos p.hw₁ hd,
           hw₂ := by simpa [Complex.div_ofReal_im] using div_neg_of_neg_of_pos p.hw₂ hd }

def Pair.scaleMass (p : Pair) (c : ℝ) (hc : 0<c) : Pair :=
  { p with a₁ := c*p.a₁, a₂ := c*p.a₂, ha₁ := mul_pos hc p.ha₁, ha₂ := mul_pos hc p.ha₂ }

/-- Four invariances required from the finite part in Lemma 2.5. Each operation has
specified masses/poles, with the strict depth and positivity conditions in Pair. -/
structure FinitePartInvariances : Prop where
  shift : ∀ (p : Pair) (x : ℝ), deficit (p.shift x).value = deficit p.value
  reflect : ∀ (p : Pair) (f : Bool), deficit (p.reflect f).value = deficit p.value
  dilate : ∀ (p : Pair) (d : ℝ) (hd : 0<d), deficit (p.dilate d hd).value = deficit p.value
  scaleMass : ∀ (p : Pair) (c : ℝ) (hc : 0<c),
    deficit (p.scaleMass c hc).value = c^2*deficit p.value

theorem ordered_representation_of_coordinate_identity (p : Pair)
    (hcoord : ∀ (f : Bool) (d : ℝ) (hd : 0<d), deficit
      ((((p.shift p.w₁.re).reflect f).dilate d hd).scaleMass (1/p.mass) (one_div_pos.mpr p.mass_pos)).value =
      (1/p.mass)^2*deficit p.value)
    (horder : p.w₂.im ≤ p.w₁.im) (hdiff : p.w₂ ≠ p.w₁) :
    ∃ γ ∈ Icc 0 (Real.pi/2), ∃ u : ℝ, 0<u ∧
      deficit p.value / p.mass^2-k₀ = margin (Real.log (p.a₂/p.a₁)) γ u := by
  let d := ‖p.w₂-p.w₁‖
  have hd : 0<d := norm_pos_iff.mpr (sub_ne_zero.mpr hdiff)
  obtain ⟨f,γ,hγ,u,hu,h₁,h₂⟩ := normalize_ordered p.hw₁ horder hdiff
  let q := (((p.shift p.w₁.re).reflect f).dilate d hd).scaleMass (1/p.mass) (one_div_pos.mpr p.mass_pos)
  obtain ⟨wa,wb⟩ := normalized_weights p.ha₁ p.ha₂
  have heq : q.value = normalSum (Real.log (p.a₂/p.a₁)) γ u := by
    funext z
    change pole ((1/p.mass)*p.a₁) (transformedPole f p.w₁.re d p.w₁) z +
      pole ((1/p.mass)*p.a₂) (transformedPole f p.w₁.re d p.w₂) z = _
    rw [h₁,h₂]
    unfold normalSum
    rw [wb,wa]
    simp only [Pair.mass,div_eq_mul_inv,one_mul,mul_one,mul_comm]
  have hdef : deficit q.value = (1/p.mass)^2*deficit p.value := hcoord f d hd
  refine ⟨γ,hγ,u,hu,?_⟩
  unfold margin
  rw [←heq,hdef]
  ring

theorem ordered_representation (hI : FinitePartInvariances) (p : Pair)
    (horder : p.w₂.im ≤ p.w₁.im) (hdiff : p.w₂ ≠ p.w₁) :
    ∃ γ ∈ Icc 0 (Real.pi/2), ∃ u : ℝ, 0<u ∧
      deficit p.value / p.mass^2-k₀ = margin (Real.log (p.a₂/p.a₁)) γ u := by
  apply ordered_representation_of_coordinate_identity p _ horder hdiff
  intro f d hd
  rw [hI.scaleMass,hI.dilate,hI.reflect,hI.shift]

theorem representation_of_invariances (hI : FinitePartInvariances) : normalizedRepresentation := by
  intro p he
  by_cases horder : p.w₂.im ≤ p.w₁.im
  · obtain ⟨γ,hγ,u,hu,eqn⟩ := ordered_representation hI p horder he.symm
    exact ⟨_,γ,u,Or.inl rfl,hγ,hu,eqn⟩
  · obtain ⟨γ,hγ,u,hu,eqn⟩ := ordered_representation hI p.swap (le_of_not_ge horder) he
    refine ⟨Real.log (p.a₁/p.a₂),γ,u,Or.inr ?_,hγ,hu,?_⟩
    · rw [Real.log_div p.ha₁.ne' p.ha₂.ne',Real.log_div p.ha₂.ne' p.ha₁.ne']; ring
    · rw [Pair.swap_value] at eqn
      simpa only [Pair.mass,Pair.swap,add_comm] using eqn

end Liu
