import Liu.LinePair
import Liu.CrossClaim

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology ComplexConjugate
namespace Liu

def poissonLine (a b x : ℝ) := b/((x-a)^2+b^2)

theorem poissonLine_of_resolvent (a b x : ℝ) : poissonLine a b x = -(linePole a b x).im := by
  simp [poissonLine,linePole,Complex.inv_im,Complex.normSq_apply,Complex.mul_im,Complex.mul_re,
    div_eq_mul_inv,pow_two]

theorem poissonLine_integral (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∫ x, poissonLine a b x = π := by
  let γ : NNReal := ⟨b,hb.le⟩
  have h (x : ℝ) : poissonLine a b x = π*ProbabilityTheory.cauchyPDFReal a γ x := by
    change b/((x-a)^2+b^2) = π*(π⁻¹*b*((x-a)^2+b^2)⁻¹)
    field_simp [pi_ne_zero]
  simp_rw [h,integral_const_mul,ProbabilityTheory.integral_cauchyPDFReal_eq_one a (show γ ≠ 0 from
    Ne.symm (ne_of_lt (show 0 < γ from hb))),mul_one]

theorem upper_resolvent_product_zero (a c : ℝ) {b d : ℝ} (hb : 0<b) (hd : 0<d)
    (hne : b ≠ d) : ∫ x, linePole a b x * linePole c d x = 0 := by
  let D : ℂ := (c-a:ℝ)+(b-d:ℝ)*Complex.I
  have hn : D ≠ 0 := fun he => by
    have hi := congrArg Complex.im he
    simp [D] at hi; exact hne (by linarith)
  have hpart (x : ℝ) : linePole a b x*linePole c d x = (linePole c d x-linePole a b x)/D := by
    let X : ℂ := ((x-a:ℝ):ℂ)+(b:ℂ)*Complex.I
    let Y : ℂ := ((x-c:ℝ):ℂ)+(d:ℂ)*Complex.I
    have hX : X ≠ 0 := fun he => by have hi := congrArg Complex.im he; simp [X] at hi; linarith
    have hY : Y ≠ 0 := fun he => by have hi := congrArg Complex.im he; simp [Y] at hi; linarith
    have hXY : D = X-Y := by dsimp [D,X,Y]; push_cast; ring
    change X⁻¹*Y⁻¹=(Y⁻¹-X⁻¹)/D
    apply (eq_div_iff hn).mpr
    rw [hXY]; field_simp [hX,hY] <;> ring
  have hi : Integrable (fun x => linePole a b x*linePole c d x) := by
    apply (linePair_integrable a c hb hd).norm.mono'
      ((linePole_continuous a hb).mul (linePole_continuous c hd)).aestronglyMeasurable
    filter_upwards with x; simp
  have he (R : ℝ) : (∫ x in -R..R, linePole a b x*linePole c d x) =
      ((∫ x in -R..R, linePole c d x) - (∫ x in -R..R, linePole a b x))/D := by
    simp_rw [hpart,div_eq_mul_inv,intervalIntegral.integral_mul_const]
    rw [intervalIntegral.integral_sub ((linePole_continuous c hd).intervalIntegrable ..)
      ((linePole_continuous a hb).intervalIntegrable ..)]
  have hh := ((linePole_principal_value c hd).sub (linePole_principal_value a hb)).div_const D
  have hh' : Tendsto (fun R : ℝ => ∫ x in -R..R, linePole a b x*linePole c d x) atTop (𝓝 0) := by
    simpa only [he,sub_self,zero_div] using hh
  exact tendsto_nhds_unique (intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id) hh'

theorem poissonLine_pair (a c : ℝ) {b d : ℝ} (hb : 0<b) (hd : 0<d) (hne : b ≠ d) :
    ∫ x, poissonLine a b x*poissonLine c d x =
      π*(b+d)/((c-a)^2+(b+d)^2) := by
  let F := linePole a b
  let G := linePole c d
  have hmix := linePair_integrable a c hb hd
  have hsame : Integrable (fun x => F x*G x) := by
    apply hmix.norm.mono' ((linePole_continuous a hb).mul (linePole_continuous c hd)).aestronglyMeasurable
    filter_upwards with x; simp [F,G]
  have h (x : ℝ) : poissonLine a b x * poissonLine c d x =
      ((F x*conj (G x)).re-(F x*G x).re)/2 := by
    rw [poissonLine_of_resolvent,poissonLine_of_resolvent]
    simp only [F,G,Complex.mul_re,Complex.conj_re,Complex.conj_im]; ring
  simp_rw [h]
  have hm : Integrable (fun x => (F x*conj (G x)).re) := Complex.reCLM.integrable_comp hmix
  have hs : Integrable (fun x => (F x*G x).re) := Complex.reCLM.integrable_comp hsame
  rw [integral_div,integral_sub hm hs]
  have h₁ := integral_re hmix
  have h₂ := integral_re hsame
  change (∫ x, (F x*conj (G x)).re) = _ at h₁
  change (∫ x, (F x*G x).re) = _ at h₂
  rw [h₁,h₂]
  dsimp only [F,G]
  rw [upper_resolvent_product_zero a c hb hd hne,linePair_integral a c hb hd]
  simp [Complex.div_re,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

/-- E.1's explicit real-part cross term, with the line pairing normalized by π. -/
theorem linePair_cross (a c : ℝ) {b d : ℝ} (hb : 0<b) (hd : 0<d) (m₁ m₂ : ℝ) :
    2*(∫ x, ((m₁:ℂ)*linePole a b x)*conj ((m₂:ℂ)*linePole c d x)).re/π =
      4*m₁*m₂*(b+d)/((c-a)^2+(b+d)^2) := by
  have h : (fun x => ((m₁:ℂ)*linePole a b x)*conj ((m₂:ℂ)*linePole c d x)) =
      fun x => ((m₁*m₂:ℝ):ℂ)*(linePole a b x*conj (linePole c d x)) := by
    funext x; simp; ring
  rw [h,integral_const_mul,linePair_integral a c hb hd]
  simp [Complex.div_re,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  field_simp [pi_ne_zero]
  <;> ring

end Liu
