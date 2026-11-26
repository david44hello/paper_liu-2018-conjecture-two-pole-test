import Liu.PhysicalBlend

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Liu

theorem normalized_smallMass_deficit {q : ℂ} (hq : q.im<0) {m : ℝ} (hm : 0 < m) (hs : m≤1/4096) :
    (38/1000:ℝ)<deficit (smallMassPair q m hq hm).value-k₀*(1+m)^2 := by
  have h10 : m≤1/10 := by linarith
  have h := blended_deficit_lower hq hm h10
  have h₁ := (abs_le.mp (smallMassFirstOrder_formula hq).2.2.2).1
  have h₂ := smallMassRemainder_bound (p:=-Complex.I) (by simp) hq hm h10
  have hnum := small_mass_arithmetic hm hs
  have hk := single_margin_lower
  have hex := mul_nonneg (sq_nonneg m) (show 0≤ singleConstant-k₀ by linarith)
  nlinarith only [h,h₂,hnum,hex,mul_le_mul_of_nonneg_left h₁ hm.le]

private theorem smallMass_deficit_ordered (p : Pair) (hs : p.a₂≤p.a₁/4096) :
    (38/1000:ℝ)*p.a₁^2<deficit p.value-k₀*p.mass^2 := by
  let m := p.a₂/p.a₁
  have hm : 0 < m := div_pos p.ha₂ p.ha₁
  have hms : m≤1/4096 := (div_le_iff₀ p.ha₁).mpr (by linarith)
  let b := -p.w₁.im
  have hb : 0<b := neg_pos.mpr p.hw₁
  let s := p.shift p.w₁.re
  let t := s.dilate b hb
  let c := p.a₁⁻¹
  have hc : 0<c := inv_pos.mpr p.ha₁
  let P := t.scaleMass c hc
  have hshift : deficit s.value=deficit p.value := (p.shift_deficit p.finite_part _).2
  have hdil : deficit t.value=deficit s.value := s.dilate_deficit s.finite_part hb
  have hmass : deficit P.value=c^2*deficit t.value := t.scaleMass_deficit t.finite_part _ hc
  have h₁ : P.a₁=1 := by change p.a₁⁻¹*p.a₁=1; exact inv_mul_cancel₀ p.ha₁.ne'
  have h₂ : P.a₂=m := by change p.a₁⁻¹*p.a₂=p.a₂/p.a₁; ring
  have hw : P.w₁= -Complex.I := by
    change (p.w₁-(p.w₁.re:ℂ))/(b:ℂ)= -Complex.I
    apply (div_eq_iff (Complex.ofReal_ne_zero.mpr hb.ne')).mpr
    dsimp [b]; apply Complex.ext <;> simp
  have hq := P.hw₂
  have he : P.value=(smallMassPair P.w₂ m hq hm).value := by
    funext z; simp only [Pair.value,smallMassPair,h₁,h₂,hw]
  have h := normalized_smallMass_deficit hq hm hms
  rw [←he,hmass,hdil,hshift] at h
  have hnorm : p.a₁^2*(1+m)^2=p.mass^2 := by
    dsimp [m,Pair.mass]; field_simp [p.ha₁.ne'] <;> ring
  have hcancel : p.a₁^2*c^2=1 := by dsimp [c]; field_simp [p.ha₁.ne']
  have hmul := mul_lt_mul_of_pos_left h (sq_pos_of_pos p.ha₁)
  nlinarith only [hmul,congrArg (fun y : ℝ => y*deficit p.value) hcancel,
    congrArg (fun y : ℝ => k₀*y) hnorm]

/-- Lemma 4.5 for arbitrary masses and pole locations, including equality in
the mass-ratio condition. -/
theorem smallMass_deficit : smallMassDeficit := by
  intro p hs
  rcases le_total p.a₂ p.a₁ with ho | ho
  · rw [min_eq_right ho,max_eq_left ho] at hs
    rw [max_eq_left ho]; exact smallMass_deficit_ordered p hs
  · rw [min_eq_left ho,max_eq_right ho] at hs
    rw [max_eq_right ho]
    have h := smallMass_deficit_ordered p.swap hs
    rw [Pair.swap_value] at h
    simpa only [Pair.swap,Pair.mass,add_comm p.a₂ p.a₁] using h

theorem Pair.small_mass_margin (p : Pair) (hs : min p.a₁ p.a₂≤ max p.a₁ p.a₂/4096) :
    (38/1000:ℝ)*(max p.a₁ p.a₂)^2<deficit p.value-k₀*p.mass^2 ∧
    0<deficit p.value/p.mass^2-k₀ := by
  have h := smallMass_deficit p hs
  refine ⟨h,sub_pos.mpr ((lt_div_iff₀ (sq_pos_of_pos p.mass_pos)).mpr ?_)⟩
  have hm : 0< max p.a₁ p.a₂ := p.ha₁.trans_le (le_max_left ..)
  linarith [mul_pos (by norm_num : (0:ℝ)<(38/1000:ℝ)) (sq_pos_of_pos hm)]

theorem pair_deficit_of_four_inputs (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) :
    k₀*p.mass^2 < deficit p.value :=
  pair_deficit_of_five_inputs p hbox hflux h54 hE4 smallMass_deficit

theorem two_pole_test_of_four_inputs (p : Pair) (hbox : Certificate.boxBounds)
    (hflux : Certificate.fluxIdentity) (h54 : Certificate.smallDepthEstimate)
    (hE4 : Certificate.mixedEdgeEstimate) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2 < deficit p.value ∧ p.slope < 0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → p.quotientDomain ε ∧ quotient (critical p ε) < k₀ :=
  two_pole_test_of_five_inputs p hbox hflux h54 hE4 smallMass_deficit

end Liu
