module

public import Liu.BoundaryL2
public import Liu.CrossClaim
public import Liu.Symmetry

@[expose] public section

noncomputable section
open Set MeasureTheory Real
open scoped ComplexConjugate
namespace Liu

def edgeCrossTrace (s γ u x : ℝ) : ℂ :=
  ∫ z, ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*crossSource (normalMass s) (direction γ) (z+(u:ℂ)*Complex.I) ∂upperArea

theorem edge_coordinates (s γ u : ℝ) :
    normalSum s γ u = fun z => normalSum s γ 0 (z+(u:ℂ)*Complex.I) := by
  funext z
  simp only [normalSum,pole,Complex.ofReal_zero,neg_zero,zero_mul,zero_add,sub_zero]
  congr 2 <;> ring

theorem reflecting_direction_coordinates (γ : ℝ) :
    direction γ = (cos γ:ℂ)-(sin γ:ℂ)*Complex.I := by
  apply Complex.ext <;> simp [direction,Complex.exp_re,Complex.exp_im,Complex.mul_re,Complex.mul_im,←Complex.ofReal_sin,←Complex.ofReal_cos]

def normalPair (s γ u : ℝ) (hγ : γ ∈ Icc 0 (π/2)) (hu : 0 < u) : Pair where
  a₁ := normalMass s
  a₂ := 1-normalMass s
  w₁ := -(u:ℂ)*Complex.I
  w₂ := -(u:ℂ)*Complex.I+direction γ
  ha₁ := Certificate.normalMass_pos _
  ha₂ := Certificate.complement_normalMass s ▸ Certificate.normalMass_pos (-s)
  hw₁ := by simp [hu]
  hw₂ := by
    simp [direction_im]
    linarith [sin_nonneg_of_nonneg_of_le_pi hγ.1 (hγ.2.trans (by linarith [pi_pos]))]

theorem normalPair_value (s γ u : ℝ) (hγ : γ ∈ Icc 0 (π/2)) (hu : 0 < u) :
    (normalPair s γ u hγ hu).toPick.value = normalSum s γ u := by
  funext z
  simp [Pair.toPick,normalPair,PickSum.value,normalSum,Fin.sum_univ_two]

theorem trace_cross_identity (s γ u x : ℝ) (z : ℂ) :
    ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*crossSource (normalMass s) (direction γ) (z+(u:ℂ)*Complex.I) =
      -Complex.I*traceDensity (normalSum s γ u) x z -
        (isolatedDensity (normalMass s) (-(u:ℂ)*Complex.I) x z:ℂ) -
        (isolatedDensity (1-normalMass s) (-(u:ℂ)*Complex.I+direction γ) x z:ℂ) := by
  have hs : source (normalSum s γ u) z = source (normalSum s γ 0) (z+(u:ℂ)*Complex.I) := by
    rw [edge_coordinates s γ u]
    simp only [source,deriv_comp_add_const]
  rw [crossSource_is_actual,traceDensity,hs]
  unfold isolatedDensity
  rw [show z-(-(u:ℂ)*Complex.I) = z+(u:ℂ)*Complex.I by ring,
    show z-(-(u:ℂ)*Complex.I+direction γ) = z+(u:ℂ)*Complex.I-direction γ by ring]
  push_cast
  ring

theorem edge_field_decomposition {s γ u : ℝ} (hγ : γ ∈ Icc 0 (π/2)) (hu : 0 < u) (x : ℝ) :
    let a := normalMass s
    let b := 1-a
    field (normalSum s γ u) x =
      -(((a*isolatedTrace 0 u x + b*isolatedTrace (cos γ) (sin γ+u) x:ℝ):ℂ) + edgeCrossTrace s γ u x) := by
  let p := normalPair s γ u hγ hu
  have hv := normalPair_value s γ u hγ hu
  have hf := p.toPick.field_on_boundary x
  have hi := p.toPick.traceDensity_integrable x
  rw [show p.toPick.value=normalSum s γ u from hv] at hi hf
  have h₁ := isolatedDensity_integral p.ha₁ p.hw₁ x
  have h₂ := isolatedDensity_integral p.ha₂ p.hw₂ x
  let i₁ := isolatedDensity p.a₁ p.w₁ x
  let i₂ := isolatedDensity p.a₂ p.w₂ x
  let D := traceDensity (normalSum s γ u) x
  have h₁c : Integrable (fun z => (i₁ z:ℂ)) upperArea := Complex.ofRealCLM.integrable_comp h₁.1
  have h₂c : Integrable (fun z => (i₂ z:ℂ)) upperArea := Complex.ofRealCLM.integrable_comp h₂.1
  have he : edgeCrossTrace s γ u x = (-Complex.I)*(∫ z, D z ∂upperArea) -
      (∫ z, (i₁ z:ℂ) ∂upperArea) - ∫ z, (i₂ z:ℂ) ∂upperArea := by
    have hd : Integrable (fun z => (-Complex.I)*D z-(i₁ z:ℂ)) upperArea :=
      (hi.const_mul (-Complex.I)).sub h₁c
    rw [edgeCrossTrace,←integral_const_mul,←integral_sub (hi.const_mul (-Complex.I)) h₁c,←integral_sub hd h₂c]
    exact integral_congr_ae (ae_of_all _ (trace_cross_identity s γ u x))
  rw [integral_complex_ofReal,integral_complex_ofReal,h₁.2,h₂.2] at he
  dsimp only [i₁,i₂,D,p,normalPair] at he
  rw [reflecting_direction_coordinates] at he
  simp only [Complex.neg_re,Complex.neg_im,Complex.mul_I_re,Complex.mul_I_im,Complex.ofReal_im,Complex.ofReal_re,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,neg_zero,neg_neg,zero_add,sub_zero,zero_sub] at he
  dsimp only
  rw [hf,he]
  change Complex.I*(∫ z, D z ∂upperArea) = _
  push_cast
  simp only [neg_add_rev,neg_neg,add_comm (cos γ) 0,zero_add,add_comm u (sin γ)]
  ring

end Liu
