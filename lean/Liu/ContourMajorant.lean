module

public import Liu.ComplexTaylorFlux

@[expose] public section

noncomputable section
open Set MeasureTheory Real
namespace Liu

def contourWeight (x : ℝ) := (1+|x|)^(-(3/2:ℝ))

theorem contourWeight_integrable : Integrable contourWeight volume := by
  change Integrable (fun x : ℝ => (1+|x|)^(-(3/2:ℝ))) volume
  simpa only [contourWeight,Real.norm_eq_abs] using
    (integrable_one_add_norm (E:=ℝ) (μ:=volume) (r:=3/2) (by norm_num))

private theorem log_tail_weight {x C : ℝ} (hx : 1≤|x|) (hC : 0≤C) :
    let U := Real.log (3*|x|/2)+π+C
    U^2/|x|^2 ≤ 4*(5+π+C)^2*contourWeight x ∧ 1/|x|^2 ≤ 4*contourWeight x := by
  let R := 1+|x|
  have hx₀ : 0 < |x| := zero_lt_one.trans_le hx
  have hR : 0<R := by dsimp [R]; positivity
  have hR₁ : 1≤R := by dsimp [R]; linarith
  have hq : 1≤R^(1/4:ℝ) := Real.one_le_rpow hR₁ (by norm_num)
  have hm : 3*|x|/2≤2*R := by dsimp [R]; linarith
  have hl := Real.log_le_log (by positivity) hm
  rw [Real.log_mul (by norm_num) hR.ne'] at hl
  have hlog := Real.log_le_rpow_div hR.le (by norm_num : (0:ℝ)<1/4)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hu : Real.log (3*|x|/2)+π+C ≤ (5+π+C)*R^(1/4:ℝ) := by
    nlinarith only [hl,hlog,h2,hq,mul_le_mul_of_nonneg_left hq pi_pos.le,mul_le_mul_of_nonneg_left hq hC]
  have hu₀ : 0≤Real.log (3*|x|/2)+π+C := by linarith [Real.log_nonneg (show 1≤3*|x|/2 by linarith),pi_pos]
  have hdiv : 1/|x| ≤ 2/R := (div_le_div_iff₀ hx₀ hR).mpr (by dsimp [R]; linarith)
  have hrpow : (R^(1/4:ℝ))^2/R^2=contourWeight x := by
    rw [←Real.rpow_mul_natCast hR.le,←Real.rpow_natCast R 2,←Real.rpow_sub hR]; norm_num [contourWeight,R]
  constructor
  · calc
      _ = (Real.log (3*|x|/2)+π+C)^2 * (1/|x|)^2 := by ring
      _ ≤ ((5+π+C)*R^(1/4:ℝ))^2*(2/R)^2 :=
        mul_le_mul (pow_le_pow_left₀ hu₀ hu _) (pow_le_pow_left₀ (by positivity) hdiv _) (sq_nonneg _) (sq_nonneg _)
      _ = _ := by rw [←hrpow]; ring
  · calc
      _ = (1/|x|)^2 := by ring
      _ ≤ (R^(1/4:ℝ))^2*(2/R)^2 := by
        have h := pow_le_pow_left₀ (by positivity) hdiv 2
        exact h.trans (le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hq))
      _ = _ := by rw [←hrpow]; ring

/-- A common integrable tail estimate on bounded sets of parameters, with
the constant-log moduli controlled on the chosen branches. -/
theorem full_contour_majorant {X x C B : ℝ} (hX : 10^18≤X) (hx : X≤|x|)
    (P Q : Fin 3 → ℂ) (a b : ℂ) (hP : ∀ i,4*‖P i‖<X) (hQ : ∀ i,4*‖Q i‖<X)
    (hc : totalLogCost P Q≤C) (hm : ‖a‖+‖b‖≤B) :
    ‖totalDensity P Q a b (x:ℂ)‖ ≤ (144*B^2*(5+π+C)^2+16*k₀*B^2)*contourWeight x := by
  let U := Real.log (3*|x|/2)+π+C
  have ha : 1≤|x| := by linarith
  have hp : 0 < |x| := zero_lt_one.trans_le ha
  have hC : 0≤C := (add_nonneg (sideLogCost_nonneg true P Q) (sideLogCost_nonneg false Q P)).trans hc
  have hB : 0≤B := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hm
  have hU : 0≤U := by dsimp [U]; linarith [pi_pos,Real.log_nonneg (show 1≤3*|x|/2 by linarith)]
  have kpos : 0≤k₀ := by unfold k₀; positivity
  have hs (s : Bool) (A D : Fin 3 → ℂ) (hA : ∀ i,4*‖A i‖<X) (hD : ∀ i,4*‖D i‖<X) (hd : sideLogCost s A D≤C) :
      ‖tailSide s A D a b x‖≤6*B*U/|x| := by
    have h := tail_side_bounds s A D a b hX hx hA hD hd
    unfold tailSide
    have hs₀ : ‖a*tailSingle s A D 0 x+b*tailSingle s A D 1 x‖ ≤ ‖a‖*(2*U/|x|)+‖b‖*(2*U/|x|) := by
      apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (h.1 0) (norm_nonneg a)) (mul_le_mul_of_nonneg_left (h.1 1) (norm_nonneg b))
    apply ((norm_add_le ..).trans (add_le_add hs₀ h.2)).trans
    calc
      _ = 6*(‖a‖+‖b‖)*U/|x| := by change ‖a‖*(2*U/|x|)+‖b‖*(2*U/|x|)+4*(‖a‖+‖b‖)*U/|x|=_; ring
      _ ≤ _ := by gcongr
  have h₁ := hs true P Q hP hQ ((le_add_of_nonneg_right (sideLogCost_nonneg false Q P)).trans hc)
  have h₂ := hs false Q P hQ hP ((le_add_of_nonneg_left (sideLogCost_nonneg true P Q)).trans hc)
  have hrat (A : Fin 3 → ℂ) (hA : ∀ i,4*‖A i‖<X) :
      ‖a*tailPole (A 0) x+b*tailPole (A 1) x‖≤2*B/|x| := by
    have bound (i : Fin 3) : ‖tailPole (A i) x‖≤2/|x| := by
      simpa [tailPole,div_eq_mul_inv,mul_comm] using inv_anti₀ (half_pos hp) (vertical_log_tail hX (hA i) hx).1
    apply (norm_add_le ..).trans; rw [norm_mul,norm_mul]
    apply (add_le_add (mul_le_mul_of_nonneg_left (bound 0) (norm_nonneg a)) (mul_le_mul_of_nonneg_left (bound 1) (norm_nonneg b))).trans
    rw [←add_mul]; apply (mul_le_mul_of_nonneg_right hm (by positivity)).trans_eq; ring
  have f := mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
  have s := mul_le_mul (hrat P hP) (hrat Q hQ) (norm_nonneg _) (by positivity)
  obtain ⟨hf,hr⟩ := log_tail_weight ha hC
  unfold totalDensity
  apply (norm_sub_le ..).trans
  simp only [norm_mul,Complex.norm_of_nonneg kpos,mul_assoc]
  calc
    _ ≤ (6*B*U/|x|)*(6*B*U/|x|)+k₀*((2*B/|x|)*(2*B/|x|)) := add_le_add f (mul_le_mul_of_nonneg_left s kpos)
    _ = (36*B^2)*(U^2/|x|^2)+(4*k₀*B^2)*(1/|x|^2) := by ring
    _ ≤ _ := by
      apply (add_le_add (mul_le_mul_of_nonneg_left hf (by positivity : 0≤36*B^2)) (mul_le_mul_of_nonneg_left hr (by positivity : 0≤4*k₀*B^2))).trans_eq
      ring

end Liu
