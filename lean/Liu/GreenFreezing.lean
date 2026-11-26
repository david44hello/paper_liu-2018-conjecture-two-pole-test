import Liu.GreenPairing
import Liu.PolarizedDefect

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

theorem PickSum.green_sources {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0<t) :
    GreenSource (dbar (logInput (p.power (1+t)))) ∧ GreenSource (p.frozenLogSource t) := by
  let K := (1+t)*p.bound^t*(p.derivativeBound/2)
  have hD : 0≤p.derivativeBound/2 := by simpa using (norm_nonneg _).trans (p.source_decay (z:=0) (by simp))
  have hK : 0≤K := by dsimp [K]; have := p.bound_pos; positivity
  have hsrc (z : ℂ) (hz : z ∈ upper) := p.power_dbar_decay ht.le (le_of_lt hz)
  constructor
  · exact GreenSource.of_decay (by linarith : 2<2+t) hK (dbar_measurable _) hsrc
  · have hv := p.power_measurable 1
    change Measurable (fun z => p.value z ^ ((1:ℝ):ℂ)) at hv
    have hm : Measurable p.value := by simpa using hv
    have hd := measurable_deriv (p.power (1+t))
    apply GreenSource.of_decay (by linarith : 2<2+t) hK (by unfold PickSum.frozenLogSource; fun_prop)
    intro z hz
    have he := p.critical_source_identity t (le_of_lt hz)
    rw [he.2]
    have h := hsrc z hz
    rw [he.1] at h
    simpa only [norm_mul,Complex.norm_conj] using h

/-- Exact real polarization of the Green form for the two physical sources,
with Fubini justified at every positive exponent. -/
theorem PickSum.green_freezing_identity {n : ℕ} (p : PickSum n) {t : ℝ} (ht : 0<t) :
    greenPairing (p.frozenLogSource t) (p.frozenLogSource t) -
        greenPairing (dbar (logInput (p.power (1+t)))) (dbar (logInput (p.power (1+t)))) =
      ∫ z, p.polarizedDefect t z ∂upperArea := by
  let a := dbar (logInput (p.power (1+t)))
  let b := p.frozenLogSource t
  let r := fun z => conj (a z)
  let d := p.frozenError t
  obtain ⟨ha,hb⟩ := p.green_sources ht
  have hr : GreenSource r := ha.conjugate
  have hd : GreenSource d := hb.sub hr
  have hbr : greenPairing d b = greenPairing b b-greenPairing r b := greenPairing_sub_left hb hr hb
  have hrr : greenPairing d r = greenPairing b r-greenPairing r r := greenPairing_sub_left hb hr hr
  have hdd : greenPairing d d = greenPairing b d-greenPairing r d := greenPairing_sub_left hb hr hd
  have hid : greenPairing b b-greenPairing a a = 2*greenPairing r d + greenPairing d d := by
    rw [←greenPairing_conj_energy a]
    change greenPairing b b-greenPairing r r=_
    linarith only [hbr,hrr,hdd,greenPairing_symm hd hb,greenPairing_symm hd hr,greenPairing_symm hr hb]
  apply hid.trans
  unfold greenPairing
  rw [←integral_const_mul,←integral_add ((greenPairing_integrable hr hd).const_mul 2) (greenPairing_integrable hd hd)]
  rfl

/-- First-order freezing for the Green energies of the actual logarithmic sources. -/
theorem PickSum.green_freezing_cost {n : ℕ} (p : PickSum n) :
    ∃ C ≥ 0, ∀ t ∈ Ioc (0:ℝ) 1, |greenPairing (p.frozenLogSource t) (p.frozenLogSource t) -
      greenPairing (dbar (logInput (p.power (1+t)))) (dbar (logInput (p.power (1+t))))| ≤ C*t := by
  obtain ⟨C,hC,h⟩ := p.polarizedDefect_integral
  refine ⟨C,hC,?_⟩
  intro t ht
  rw [p.green_freezing_identity ht.1]
  exact (h t ⟨ht.1.le,ht.2⟩).2

end Liu
