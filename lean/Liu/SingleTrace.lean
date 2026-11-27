module

public import Liu.TraceSlices

@[expose] public section

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

/-- The positive scalar trace for a unit mass at a−ib. -/
def isolatedTrace (a b x : ℝ) : ℝ := ∫ t in Ioi b, poissonLine a t x/(t+b)

private theorem affine_halfline_substitution (b : ℝ) (f : ℝ → ℝ) :
    ∫ t in Ioi b, f t = ∫ y in Ioi (0:ℝ), 2*f (2*y+b) := by
  let φ := fun y : ℝ => 2*y+b
  have img : φ '' Ioi 0 = Ioi b := by
    ext t
    constructor
    · rintro ⟨y,hy,rfl⟩
      change b < 2*y+b
      change 0 < y at hy
      linarith
    · intro ht
      change b<t at ht
      exact ⟨(t-b)/2,show 0 < (t-b)/2 by linarith,by dsimp [φ]; ring⟩
  have der (y : ℝ) (_hy : y ∈ Ioi 0) : HasDerivWithinAt φ 2 (Ioi 0) y := by
    simpa [φ] using (((hasDerivAt_id y).const_mul 2).add_const b).hasDerivWithinAt (s:=Ioi 0)
  have inj : InjOn φ (Ioi 0) := by intro x _ y _ h; dsimp [φ] at h; linarith
  rw [←img,integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi der inj]
  simp [φ,smul_eq_mul]

private theorem single_trace_slice (a x : ℝ) {m b y : ℝ} (hm : 0 < m) (hb : 0 < b) (hy : 0<y) :
    ∫ X : ℝ, traceDensity (pole m ((a:ℂ)-(b:ℂ)*Complex.I)) x ⟨X,y⟩ =
      Complex.I*(m:ℂ)*((π*(poissonLine a (2*y+b) x/(y+b)):ℝ):ℂ) := by
  let w : ℂ := (a:ℂ)-(b:ℂ)*Complex.I
  have hsep (X : ℝ) : (⟨X,y⟩:ℂ) ≠ w := fun he => by
    have h := congrArg Complex.im he; simp [w] at h; linarith
  have hn (X : ℝ) : ‖(⟨X,y⟩:ℂ)-w‖^2 = (X-a)^2+(y+b)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [w,pow_two] <;> ring
  have hn' (X : ℝ) : ‖(⟨X,y⟩:ℂ)-(x:ℂ)‖^2 = (X-x)^2+y^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [pow_two]
  have hj (X : ℝ) : traceDensity (pole m w) x ⟨X,y⟩ =
      (Complex.I*(m:ℂ)/((y+b:ℝ):ℂ)) * ((poissonLine x y X * poissonLine a (y+b) X:ℝ):ℂ) := by
    simp only [traceDensity,singlePole_source hm (hsep X),hn X,hn' X,poissonLine]
    push_cast
    have hd : (y:ℂ)+(b:ℂ) ≠ 0 := by exact_mod_cast (add_pos hy hb).ne'
    field_simp [hd] <;> ring
  change (∫ X : ℝ, traceDensity (pole m w) x ⟨X,y⟩) = _
  simp_rw [hj,integral_const_mul,integral_complex_ofReal]
  rw [poissonLine_pair x a hy (add_pos hy hb) (by linarith)]
  simp only [poissonLine,show y+(y+b)=2*y+b by ring,show (a-x)^2=(x-a)^2 by ring]
  push_cast
  ring

theorem field_single_pole (a x : ℝ) {m b : ℝ} (hm : 0 < m) (hb : 0 < b) :
    field (pole m ((a:ℂ)-(b:ℂ)*Complex.I)) x = -(m:ℂ)*(isolatedTrace a b x:ℂ) := by
  let p := singlePick m a b hm hb
  let S := pole m ((a:ℂ)-(b:ℂ)*Complex.I)
  have hv : p.value = S := singlePick_value .. 
  have hf := p.field_on_boundary x
  have hi := p.traceDensity_integrable x
  rw [hv] at hf hi
  change field S x = _
  rw [hf]
  change Complex.I*(∫ z, traceDensity S x z ∂upperArea) = _
  rw [upperArea_slices _ hi]
  have he : (∫ y in Ioi (0:ℝ), ∫ X : ℝ, traceDensity S x ⟨X,y⟩) =
      ∫ y in Ioi (0:ℝ), (Complex.I*(m:ℂ)*(π:ℂ))*((poissonLine a (2*y+b) x/(y+b):ℝ):ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [single_trace_slice a x hm hb hy]
    push_cast
    ring
  rw [he,integral_const_mul,integral_complex_ofReal]
  have ht : isolatedTrace a b x = ∫ y in Ioi (0:ℝ), poissonLine a (2*y+b) x/(y+b) := by
    rw [isolatedTrace,affine_halfline_substitution]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    have hden : 0 < y+b := add_pos hy hb
    rw [show 2*y+b+b=2*(y+b) by ring]
    field_simp [hden.ne']
  rw [←ht,Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr pi_ne_zero]
  linear_combination (m:ℂ)*(isolatedTrace a b x:ℂ)*Complex.I_sq

theorem isolatedTrace_nonneg (a x : ℝ) {b : ℝ} (hb : 0 < b) : 0 ≤ isolatedTrace a b x := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have h := hb.trans ht
  unfold poissonLine; positivity

end Liu
