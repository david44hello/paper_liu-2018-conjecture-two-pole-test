module

public import Liu.LogSource

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace Liu

private theorem centered_variance {n : ℕ} (a u : Fin n → ℂ) (c : ℂ) :
    (∑ i, a i)*(∑ i, a i*(u i)^2) - (∑ i, a i*u i)^2 =
      (∑ i, a i)*(∑ i, a i*(u i-c)^2) - (∑ i, a i*(u i-c))^2 := by
  have h₁ (i) : a i*(u i-c) = a i*u i-a i*c := by ring
  have h₂ (i) : a i*(u i-c)^2 = a i*(u i)^2-(a i*u i)*(2*c)+a i*c^2 := by ring
  simp_rw [h₁,h₂]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  simp only [←Finset.sum_mul]
  ring

/-- Cancellation of the two leading orders in m S' − S². The reference pole at
−i is used only to center the resolvents, and contributes no mass. -/
theorem PickSum.derivative_quartic_defect {n : ℕ} (p : PickSum n) :
    ∃ K > 0, ∀ z : ℂ, 0 ≤ z.im →
      ‖(p.mass:ℂ)*deriv p.value z-(p.value z)^2‖ ≤ K/(1+‖z‖)^4 := by
  let w₀ := -Complex.I
  have hw₀ : w₀.im < 0 := by simp [w₀]
  let A := fun i => p.weight i
  let B := fun i => ‖p.location i-w₀‖*poleBound 1 (p.location i)*poleBound 1 w₀
  let B₁ := ∑ i, A i*B i
  let B₂ := ∑ i, A i*(B i)^2
  have h₂ : 0≤B₂ := Finset.sum_nonneg (fun i _ => mul_nonneg (p.pos i).le (sq_nonneg _))
  have hm := p.mass_pos
  refine ⟨1+p.mass*B₂+B₁^2,by positivity,?_⟩
  intro z hz
  let R := 1+‖z‖
  have hR : 0<R := by dsimp [R]; positivity
  let u := fun i => (z-p.location i)⁻¹
  let c := (z-w₀)⁻¹
  have sep {w : ℂ} (hw : w.im<0) : z-w≠0 := fun he => by
    have h := congrArg Complex.im (sub_eq_zero.mp he); linarith
  have unit {w : ℂ} (hw : w.im < 0) : ‖(z-w)⁻¹‖ ≤ poleBound 1 w/R := by
    simpa only [pole,Complex.ofReal_one,norm_div,norm_neg,norm_one,one_div,norm_inv] using
      pole_global_decay (a:=1) (by norm_num) hw hz
  have delta (i) : ‖u i-c‖ ≤ B i/R^2 := by
    have he : u i-c = (p.location i-w₀)*(z-p.location i)⁻¹*(z-w₀)⁻¹ := by
      dsimp [u,c]; field_simp [sep (p.below i),sep hw₀]; ring
    rw [he,norm_mul,norm_mul]
    calc
      _ ≤ (‖p.location i-w₀‖*(poleBound 1 (p.location i)/R))*(poleBound 1 w₀/R) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (unit (p.below i)) (norm_nonneg _)) (unit hw₀)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (unit (p.below i))))
      _ = _ := by dsimp [B]; ring
  have hv : p.value z = -(∑ i, (A i:ℂ)*u i) := by
    simp only [PickSum.value,pole,div_eq_mul_inv,A,u,neg_mul,Finset.sum_neg_distrib]
  have hd : deriv p.value z = ∑ i, (A i:ℂ)*(u i)^2 := by
    rw [(p.hasDerivAt hz).deriv]; simp [A,u,div_eq_mul_inv]
  have hmass : (p.mass:ℂ) = ∑ i, (A i:ℂ) := by simp [PickSum.mass,A]
  have hsum : ‖∑ i, (A i:ℂ)*(u i-c)‖ ≤ B₁/R^2 := by
    rw [show B₁/R^2 = ∑ i, (A i*B i)/R^2 from Finset.sum_div ..]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_mul,Complex.norm_of_nonneg (p.pos i).le,mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (delta i) (p.pos i).le
  have hsq : ‖∑ i, (A i:ℂ)*(u i-c)^2‖ ≤ B₂/R^4 := by
    rw [show B₂/R^4 = ∑ i, (A i*B i^2)/R^4 from Finset.sum_div ..]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_mul,norm_pow,Complex.norm_of_nonneg (p.pos i).le,mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (p.pos i).le
    have h := pow_le_pow_left₀ (norm_nonneg _) (delta i) 2
    simpa only [div_pow,←pow_mul] using h
  rw [hv,hd,hmass,neg_sq,centered_variance (fun i => (A i:ℂ)) u c,←hmass]
  apply (norm_sub_le ..).trans
  rw [norm_mul,Complex.norm_of_nonneg hm.le,norm_pow]
  have hsum₂ := pow_le_pow_left₀ (norm_nonneg _) hsum 2
  rw [div_pow,←pow_mul] at hsum₂
  change _ ≤ B₁^2/R^4 at hsum₂
  calc
    _ ≤ p.mass*(B₂/R^4)+B₁^2/R^4 := add_le_add (mul_le_mul_of_nonneg_left hsq hm.le) hsum₂
    _ ≤ _ := by
      change _ ≤ (1+p.mass*B₂+B₁^2)/R^4
      rw [←mul_div_assoc,←add_div]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end Liu
