module

public import Liu.FieldBound
public import Liu.DeficitRemainder

@[expose] public section

noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate
namespace Liu

theorem field_measurable (S : ℂ → ℂ) : Measurable (field S) := by
  have h1 := measurable_fderiv_apply_const ℝ (potential S) (1:ℂ)
  have hI := measurable_fderiv_apply_const ℝ (potential S) Complex.I
  unfold field; fun_prop

/-- The locally truncated physical deficit is absolutely integrable at every radius. -/
theorem PickSum.deficit_local_integrable {n : ℕ} (p : PickSum n) (R : ℝ) :
    IntegrableOn (fun z => k₀*‖p.value z‖^2-‖field p.value z‖^2) (halfDisc R) area := by
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  obtain ⟨C,hC,hv⟩ := p.field_bounded_upper
  have hs := p.power_measurable 1
  change Measurable (fun z => p.value z^((1:ℝ):ℂ)) at hs
  have hs' : Measurable p.value := by simpa using hs
  have hf := field_measurable p.value
  have hM : MeasurableSet (halfDisc R) := upper_open.measurableSet.inter Metric.isOpen_ball.measurableSet
  have hfin := measure_ne_top_of_subset (μ:=area) (show halfDisc R ⊆ ball 0 R from inter_subset_right) (measure_ball_lt_top ..).ne
  have hk : 0≤k₀ := by unfold k₀; positivity
  apply (integrableOn_const (C:=k₀*p.bound^2+C^2) hfin).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem (μ:=area) hM] with z hz
  have h := (p.global_decay (le_of_lt hz.1)).trans (div_le_self p.bound_pos.le (by linarith [norm_nonneg z]))
  have hs0 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 2) hk
  have hv0 := pow_le_pow_left₀ (norm_nonneg _) (hv z hz.1) 2
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg ‖field p.value z‖,sq_nonneg C,mul_nonneg hk (sq_nonneg ‖p.value z‖),
    mul_nonneg hk (sq_nonneg p.bound)]

def fieldFarModel (m : ℝ) (z : ℂ) : ℂ := ((-m*(π/2-z.arg):ℝ):ℂ)/z

private theorem model_norm (m : ℝ) (hm : 0 ≤ m) (z : ℂ) :
    ‖fieldFarModel m z‖ = m*|π/2-z.arg|/‖z‖ := by
  rw [fieldFarModel,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg hm]

/-- The uniform field estimate in Lemma 2.3 is the only outstanding input here.
The local integrability, radial cancellation and tail comparison are proved. -/
theorem PickSum.finitePart_of_field_asymptotic {n : ℕ} (p : PickSum n) {T K : ℝ} (hK : 0≤K)
    (hfar : ∀ z ∈ upper, T ≤ ‖z‖ → ‖field p.value z-fieldFarModel p.mass z‖ ≤ K*(1+log ‖z‖)/‖z‖^2) :
    finitePartExists p.value ∧ deficit p.value=∫ z, finitePartRemainder p.value p.mass z ∂upperArea := by
  apply finitePart_of_integrable_remainder
  let R := 2+max 0 T
  let D := p.mass*(3*π/2)
  have hD : 0≤D := by have := p.mass_pos; dsimp [D]; positivity
  have hk : 0≤k₀ := by unfold k₀; positivity
  obtain ⟨A,hA,hS⟩ := p.power_tail_error
  let L := k₀*A+K*(K+2*D)
  have hL : 0≤L := by dsimp [L]; positivity
  have hlocal : IntegrableOn (finitePartRemainder p.value p.mass) (halfDisc R) area :=
    (p.deficit_local_integrable R).sub (leadingDeficit_integrableOn p.mass R)
  let tail := upper \ ball (0:ℂ) R
  have hM : MeasurableSet tail := upper_open.measurableSet.diff Metric.isOpen_ball.measurableSet
  have hs := p.power_measurable 1
  change Measurable (fun z => p.value z^((1:ℝ):ℂ)) at hs
  have hm : Measurable p.value := by simpa using hs
  have hf := field_measurable p.value
  have hrad : Measurable (radialTail 2) := by
    unfold radialTail
    apply Measurable.ite (measurableSet_lt measurable_const measurable_norm) (by fun_prop) measurable_const
  have hrem : Measurable (finitePartRemainder p.value p.mass) := by unfold finitePartRemainder leadingDeficit angularDeficit; fun_prop
  have htl : IntegrableOn (finitePartRemainder p.value p.mass) tail area := by
    apply ((show IntegrableOn _ upper area from logTail_integrable.const_mul (8*L)).mono_set sdiff_subset).mono' hrem.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ:=area) hM] with z hz
    let r := ‖z‖
    have hrR : R ≤ r := by simpa [r] using hz.2
    have hT : T≤r := by dsimp [R] at hrR; linarith [le_max_right 0 T]
    have hr : 1<r := by dsimp [R] at hrR; linarith [le_max_left 0 T]
    have hp := zero_lt_one.trans hr
    have hlog := log_nonneg hr.le
    let u := fieldFarModel p.mass z
    let v := field p.value z
    have hu : ‖u‖≤D/r := by
      rw [show ‖u‖ = _ from model_norm _ p.mass_pos.le z]
      have hi := abs_le.mp (Complex.abs_arg_le_pi z)
      apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left _ p.mass_pos.le) hp.le
      exact abs_le.mpr ⟨by linarith [pi_pos],by linarith [pi_pos]⟩
    have he : ‖v-u‖ ≤ K*(1+log r)/r^2 := hfar z hz.1 hT
    have he' : ‖v-u‖ ≤ K/r := he.trans (by
      have hh := log_le_sub_one_of_pos hp
      apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
      nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show 1+log r ≤ r by linarith) hK) hp.le])
    have hv : ‖v‖ ≤ (K+D)/r := by
      have hh := norm_add_le (v-u) u
      rw [sub_add_cancel] at hh
      exact hh.trans ((add_le_add he' hu).trans_eq (add_div ..).symm)
    have hdiff : |‖v‖^2-‖u‖^2| ≤ K*(K+2*D)*(1+log r)/r^3 := by
      rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      have hsum : ‖v‖+‖u‖ ≤ (K+2*D)/r := (add_le_add hv hu).trans_eq (by ring)
      rw [mul_comm (‖v‖+‖u‖)]
      apply (mul_le_mul ((abs_norm_sub_norm_le ..).trans he) hsum (by positivity) (by positivity)).trans_eq
      field_simp [hp.ne'] <;> ring
    have hs := hS 2 (by constructor <;> norm_num) z (le_of_lt hz.1) hr
    simp only [rpow_neg (norm_nonneg z),rpow_ofNat] at hs
    have heq : finitePartRemainder p.value p.mass z =
        k₀*(‖p.value z‖^2-p.mass^2*(r^2)⁻¹)-(‖v‖^2-‖u‖^2) := by
      dsimp only [finitePartRemainder,leadingDeficit,angularDeficit,radialTail,v,u]
      rw [if_pos hr,rpow_neg hp.le,rpow_ofNat,model_norm _ p.mass_pos.le,div_pow,mul_pow,sq_abs]
      dsimp only [r]; ring
    rw [Real.norm_eq_abs,heq]
    apply (abs_sub ..).trans
    rw [abs_mul,abs_of_nonneg hk]
    have hraw := add_le_add (mul_le_mul_of_nonneg_left hs hk) hdiff
    apply hraw.trans
    have hlog' := log_le_log hp (show r≤2+r by linarith)
    have hnn : 1≤1+log (2+r) := by linarith
    have hgeom := pow_le_pow_left₀ (by positivity : 0≤1+r) (by linarith : 1+r≤2*r) 3
    change k₀*(A*(r^3)⁻¹)+K*(K+2*D)*(1+log r)/r^3 ≤ 8*L*((1+log (2+r))/(1+r)^3)
    have hnum : k₀*A+K*(K+2*D)*(1+log r) ≤ L*(1+log (2+r)) := by
      dsimp [L]
      nlinarith only [mul_le_mul_of_nonneg_left hnn (mul_nonneg hk hA),
        mul_le_mul_of_nonneg_left hlog' (mul_nonneg hK (by positivity : 0≤K+2*D))]
    calc
      _ = (k₀*A+K*(K+2*D)*(1+log r))/r^3 := by ring
      _ ≤ _ := by
        apply (div_le_div_of_nonneg_right hnum (by positivity)).trans
        rw [←mul_div_assoc (8*L) (1+log (2+r)) ((1+r)^3)]
        apply (div_le_div_iff₀ (pow_pos hp _) (by positivity)).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hgeom (show 0≤L*(1+log (2+r)) by positivity)]
  exact (hlocal.union htl).mono_set (fun z hz => by
    by_cases h : z ∈ ball (0:ℂ) R
    · exact Or.inl ⟨hz,h⟩
    · exact Or.inr ⟨hz,h⟩)

end Liu
