module

public import Liu.EdgeTrace

@[expose] public section

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

def edgeFluxTerms (s γ u x : ℝ) : ℝ :=
  let A := normalMass s * isolatedTrace 0 u x
  let B := (1-normalMass s) * isolatedTrace (cos γ) (sin γ+u) x
  let Z := edgeCrossTrace s γ u x
  2*A*B + 2*(A+B)*Z.re + Z.re^2 + Z.im^2

private theorem isolated_sq_int (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x => (isolatedTrace a b x)^2) :=
  (memLp_two_iff_integrable_sq (isolatedTrace_memLp a hb).aestronglyMeasurable).mp (isolatedTrace_memLp a hb)

private theorem single_line_cancellation (a : ℝ) {b : ℝ} (hb : 0<b) (m : ℝ) :
    (∫ x, (m*isolatedTrace a b x)^2) = k₀*(∫ x, ‖(m:ℂ)*linePole a b x‖^2) := by
  simp_rw [mul_pow,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,integral_const_mul]
  rw [(div_eq_iff pi_ne_zero).mp (isolatedTrace_energy a hb),linePole_square_integral a hb]
  ring

/-- Appendix E.1, including absolute convergence of the displayed real integral
and the exact cross pairing of the two isolated analytic poles. -/
theorem edge_flux_decomposition {s γ u : ℝ} (hγ : γ ∈ Icc 0 (π/2)) (hu : 0 < u) :
    Integrable (edgeFluxTerms s γ u) ∧
    flux s γ u = (∫ x, edgeFluxTerms s γ u x)/π -
      k₀*(4*normalMass s*(1-normalMass s)*(sin γ+2*u)/(cos γ^2+(sin γ+2*u)^2)) := by
  let a := normalMass s
  let b := 1-a
  let d := sin γ+u
  have hsin := sin_nonneg_of_nonneg_of_le_pi hγ.1 (hγ.2.trans (by linarith [pi_pos]))
  have hd : 0 < d := add_pos_of_nonneg_of_pos hsin hu
  let A := fun x => a * isolatedTrace 0 u x
  let B := fun x => b * isolatedTrace (cos γ) d x
  let P := fun x => (a:ℂ)*linePole 0 u x
  let Q := fun x => (b:ℂ)*linePole (cos γ) d x
  let C := fun x => (P x * conj (Q x)).re
  let V := fun x : ℝ => field (normalSum s γ u) x
  have hfield (x : ℝ) : ‖V x‖^2 = A x^2+B x^2+edgeFluxTerms s γ u x := by
    have h := edge_field_decomposition (s:=s) hγ hu x
    change ‖field (normalSum s γ u) x‖^2 = _
    rw [h,norm_neg,Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,zero_add]
    dsimp [A,B,a,b,d,edgeFluxTerms]
    ring
  have hval (x : ℝ) : normalSum s γ u x = -(P x+Q x) := by
    have hp₁ : -(u:ℂ)*Complex.I = (0:ℂ)-(u:ℂ)*Complex.I := by ring
    have hp₂ : -(u:ℂ)*Complex.I+direction γ = ((cos γ:ℝ):ℂ)-(d:ℂ)*Complex.I := by
      rw [reflecting_direction_coordinates]; dsimp [d]; push_cast; ring
    unfold normalSum
    rw [hp₂,hp₁]
    change pole a ((0:ℝ)-(u:ℂ)*Complex.I) x + pole b ((cos γ:ℝ)-(d:ℂ)*Complex.I) x = _
    rw [pole_on_line,pole_on_line]; dsimp [P,Q]; ring
  have hsSq (x : ℝ) : ‖normalSum s γ u x‖^2 = ‖P x‖^2+‖Q x‖^2+2*C x := by
    rw [hval,norm_neg]
    simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
      C,Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  have hpInt (r t m : ℝ) (ht : 0<t) : Integrable (fun x => ‖(m:ℂ)*linePole r t x‖^2) := by
    simpa only [norm_mul,mul_pow] using (linePole_sq_integrable r ht).const_mul (‖(m:ℂ)‖^2)
  have hP := hpInt 0 u a hu
  have hQ := hpInt (cos γ) d b hd
  have hprod : Integrable (fun x => P x*conj (Q x)) := by
    have h := (linePair_integrable 0 (cos γ) hu hd).const_mul ((a:ℂ)*(b:ℂ))
    apply h.congr; filter_upwards with x
    simp [P,Q]; ring
  have hC : Integrable C := Complex.reCLM.integrable_comp hprod
  have hS : Integrable (fun x : ℝ => ‖normalSum s γ u x‖^2) := by
    simp_rw [hsSq]
    exact (hP.add hQ).add (hC.const_mul 2)
  have hV' := (normalPair s γ u hγ hu).toPick.field_memLp_boundary
  rw [normalPair_value] at hV'
  have hV : Integrable (fun x => ‖V x‖^2) :=
    (memLp_two_iff_integrable_sq_norm hV'.aestronglyMeasurable).mp hV'
  have hA : Integrable (fun x => A x^2) := by simpa only [A,mul_pow] using (isolated_sq_int 0 hu).const_mul (a^2)
  have hB : Integrable (fun x => B x^2) := by simpa only [B,mul_pow] using (isolated_sq_int (cos γ) hd).const_mul (b^2)
  have hE : Integrable (edgeFluxTerms s γ u) := by
    apply ((hV.sub hA).sub hB).congr
    filter_upwards with x
    change ‖V x‖^2 - A x^2-B x^2 = _
    rw [hfield]; ring
  refine ⟨hE,?_⟩
  have eV : (∫ x, ‖V x‖^2) = (∫ x, A x^2)+(∫ x, B x^2)+∫ x, edgeFluxTerms s γ u x := by
    simp_rw [hfield]
    rw [integral_add (f:=fun x => A x^2+B x^2) (hA.add hB) hE,integral_add hA hB]
  have eS : (∫ x : ℝ, ‖normalSum s γ u x‖^2) = (∫ x, ‖P x‖^2)+(∫ x, ‖Q x‖^2)+2*(∫ x, C x) := by
    simp_rw [hsSq]
    rw [integral_add (f:=fun x => ‖P x‖^2+‖Q x‖^2) (hP.add hQ) (hC.const_mul 2),
      integral_add hP hQ,integral_const_mul]
  have ec : 2*(∫ x, C x)/π = 4*a*b*(sin γ+2*u)/(cos γ^2+(sin γ+2*u)^2) := by
    have he : (∫ x, C x) = (∫ x, P x*conj (Q x)).re := integral_re hprod
    rw [he]
    simpa only [sub_zero,show u+d=sin γ+2*u by dsimp [d];ring,P,Q] using
      linePair_cross 0 (cos γ) hu hd a b
  have eA : (∫ x, A x^2)=k₀*(∫ x, ‖P x‖^2) := single_line_cancellation 0 hu a
  have eB : (∫ x, B x^2)=k₀*(∫ x, ‖Q x‖^2) := single_line_cancellation (cos γ) hd b
  change (∫ x, ‖V x‖^2-k₀*‖normalSum s γ u x‖^2)/π = _ - k₀*(4*a*b*(sin γ+2*u)/(cos γ^2+(sin γ+2*u)^2))
  rw [integral_sub hV (hS.const_mul k₀),integral_const_mul,eV,eS,eA,eB,←ec]
  ring

end Liu
