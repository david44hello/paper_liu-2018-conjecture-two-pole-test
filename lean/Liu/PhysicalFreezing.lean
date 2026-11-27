module

public import Liu.SupercriticalProjection
public import Liu.GreenFreezing

@[expose] public section

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology ComplexConjugate
namespace Liu

theorem PickSum.supercritical_sources {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    SupercriticalSource (dbar (logInput (p.power (1+t)))) t ∧ SupercriticalSource (p.frozenLogSource t) t := by
  let K := (1+t)*p.bound^t*(p.derivativeBound/2)
  have hD : 0≤p.derivativeBound/2 := by simpa using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  have hK : 0≤K := by dsimp [K]; have := p.bound_pos; positivity
  have hs (w : ℂ) (hw : w∈upper) := p.power_dbar_decay ht.le (le_of_lt hw)
  obtain ⟨ha,hb⟩ := p.green_sources ht
  refine ⟨⟨ht,ht1,ha.measurable,K,hK,hs⟩,⟨ht,ht1,hb.measurable,K,hK,?_⟩⟩
  intro w hw
  obtain ⟨he,hf⟩ := p.critical_source_identity t (le_of_lt hw)
  have hh := hs w hw
  rw [he] at hh
  rw [hf]
  simpa only [norm_mul,Complex.norm_conj] using hh

private theorem logInput_differentiable {g : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℂ g z) (hn : g z≠0) :
    DifferentiableAt ℝ (logInput g) z := by
  have hreal := hd.restrictScalars ℝ
  have hl := (hreal.norm ℝ hn).log (norm_ne_zero_iff.mpr hn)
  exact hreal.mul (Complex.ofRealCLM.differentiableAt.comp z hl)

private theorem quotient_conjugate_differentiable {g : ℂ → ℂ} {z : ℂ} (dh : DifferentiableAt ℂ g z) (hn : g z≠0) :
    DifferentiableAt ℝ (fun w => g w/conj (g w)) z := by
  have dr := dh.restrictScalars ℝ
  have dc : DifferentiableAt ℝ (fun w => conj (g w)) z := Complex.conjCLE.differentiableAt.comp z dr
  simpa only [div_eq_mul_inv,Pi.mul_def,Pi.inv_def] using dr.mul (dc.inv ((map_ne_zero (starRingEnd ℂ)).mpr hn))

theorem PickSum.log_sources_differentiable {n : ℕ} (p : PickSum n) (t : ℝ) :
    DifferentiableOn ℝ (dbar (logInput (p.power (1+t)))) upper ∧ DifferentiableOn ℝ (p.frozenLogSource t) upper := by
  let g := p.power (1+t)
  have dg (z : ℂ) (hz : z∈upper) : DifferentiableAt ℂ g z := (p.power_hasDerivAt t (le_of_lt hz)).differentiableAt
  have hol : DifferentiableOn ℂ g upper := fun z hz => (dg z hz).differentiableWithinAt
  have hcd (z : ℂ) (hz : z∈upper) : DifferentiableAt ℝ (fun u => conj (deriv g u)) z :=
    Complex.conjCLE.differentiableAt.comp z (((hol.deriv upper_open).differentiableAt (upper_open.mem_nhds hz)).restrictScalars ℝ)
  constructor
  · intro z hz
    have d := ((quotient_conjugate_differentiable (dg z hz) (p.power_nonzero (1+t) (le_of_lt hz))).const_mul (1/2:ℂ)).mul (hcd z hz)
    apply d.differentiableWithinAt.congr
    · intro w hw
      exact dbar_logInput (dg w hw).hasDerivAt (p.power_nonzero _ (le_of_lt hw))
    · exact dbar_logInput (dg z hz).hasDerivAt (p.power_nonzero _ (le_of_lt hz))
  · intro z hz
    have hn : p.value z≠0 := fun he => by have hi := p.value_im_pos (le_of_lt hz); simp [he] at hi
    exact (((quotient_conjugate_differentiable (p.hasDerivAt (le_of_lt hz)).differentiableAt hn).const_mul (1/2:ℂ)).mul (hcd z hz)).differentiableWithinAt

theorem PickSum.log_residual_eq_field {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    let h := logInput (p.power (1+t))
    asL2 h-project (asL2 h)=asL2 (canonicalField (dbar h)) := by
  exact (p.supercritical_sources ht ht1).1.residual_eq_field (p.log_sources_differentiable t).1
    (p.log_power_memLp_two (by linarith)) (fun z hz => (logInput_differentiable
      (p.power_hasDerivAt t (le_of_lt hz)).differentiableAt (p.power_nonzero _ (le_of_lt hz))).differentiableWithinAt)
    (fun _ _ => rfl)

/-- Step 2 for the genuine projection numerator and the energy of the frozen field. -/
theorem PickSum.physical_freezing_cost {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ t ∈ Ioo (0:ℝ) 1, let u := asL2 (logInput (p.power (1+t)))
      |energy (canonicalField (p.frozenLogSource t))-‖u-project u‖^2| ≤ C*t := by
  obtain ⟨A,hA,ha⟩ := p.green_freezing_cost
  refine ⟨4*A,by positivity,?_⟩
  intro t ht
  obtain ⟨a,b⟩ := p.supercritical_sources ht.1 ht.2
  obtain ⟨da,db⟩ := p.log_sources_differentiable t
  dsimp only
  rw [p.log_residual_eq_field ht.1 ht.2,←energy,b.energy_eq_green db,a.energy_eq_green da,←mul_sub,abs_mul]
  norm_num
  linarith only [ha t ⟨ht.1,ht.2.le⟩]

/-- Equation (frozen) with its quadratic error in the actual quotient. -/
theorem PickSum.quotient_freezing_cost {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ᶠ t in 𝓝[>] (0:ℝ),
      |quotient (p.power (1+t)) - energy (canonicalField (p.frozenLogSource t))/energy (p.power (1+t))| ≤ C*t^2 := by
  obtain ⟨A,hA,ha⟩ := p.physical_freezing_cost
  let m := p.mass^2/4
  have hm : 0 < m := by dsimp [m]; have := p.mass_pos; positivity
  have hL := p.denominator_limit.eventually_const_lt (show m < p.mass^2/2 by dsimp [m]; linarith [sq_pos_of_pos p.mass_pos])
  refine ⟨A/m,div_nonneg hA hm.le,?_⟩
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  filter_upwards [hL,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),hid.eventually_lt_const zero_lt_one] with t hden ht ht1
  change 0<t at ht
  let E := energy (p.power (1+t))
  change m<t*E at hden
  have hE : 0<E := by by_contra! hh; linarith [mul_nonpos_of_nonneg_of_nonpos ht.le hh]
  have hb := ha t ⟨ht,ht1⟩
  dsimp only at hb
  unfold quotient
  change |_/E-_/E|≤_
  rw [←sub_div,abs_div,abs_of_pos hE,abs_sub_comm]
  apply (div_le_div_of_nonneg_right hb hE.le).trans
  apply (div_le_iff₀ hE).mpr
  calc
    A*t = (A/m*t)*m := by field_simp [hm.ne']
    _ ≤ (A/m*t)*(t*E) := mul_le_mul_of_nonneg_left hden.le (by positivity)
    _ = _ := by ring

end Liu
