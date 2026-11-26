import Liu.BlendedWitness
import Liu.SmallRemainder

noncomputable section
open Set Real MeasureTheory Filter Metric
open scoped ComplexConjugate Topology
namespace Liu

def firstOrderQ (ι : ℂ) : ℂ := ((k₀-‖ι‖^2:ℝ):ℂ)-Complex.I*(ι.re:ℂ)

def firstOrderIntegrand (p q : ℂ) (z : ℂ) : ℂ :=
  let A := pole 1 p
  let B := pole 1 q
  A z*conj (B z-A z)*firstOrderQ (((A z).arg:ℂ)-optimalWitness A z)

theorem firstOrderQ_bound {p z : ℂ} (hp : p.im<0) (hz : 0≤z.im) :
    ‖firstOrderQ (((pole 1 p z).arg:ℂ)-optimalWitness (pole 1 p) z)‖ ≤ 5 := by
  have he : (p.re:ℂ)-((-p.im:ℝ):ℂ)*Complex.I=p := by apply Complex.ext <;> simp
  have h := singlePole_witness_bounds p.re zero_lt_one (neg_pos.mpr hp) hz
  dsimp only at h; rw [he] at h
  let ι := ((pole 1 p z).arg:ℂ)-optimalWitness (pole 1 p) z
  have hr : |ι.re|≤2.264 := h.2.2.1.le
  have hu : |k₀-‖ι‖^2|≤4.304 := h.2.2.2.le
  change ‖firstOrderQ ι‖≤5
  apply le_of_sq_le_sq _ (by norm_num)
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp only [firstOrderQ,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Complex.sub_im,Complex.mul_im,one_mul,zero_add,zero_sub]
  nlinarith only [sq_abs ι.re,sq_abs (k₀-‖ι‖^2),pow_le_pow_left₀ (abs_nonneg _) hr 2,
    pow_le_pow_left₀ (abs_nonneg _) hu 2]

theorem firstOrderIntegrand_bound {p q z : ℂ} (hp : p.im<0) (hq : q.im<0) (hz : 0≤z.im) :
    ‖firstOrderIntegrand p q z‖≤5*‖q-p‖/(‖z-p‖^2*‖z-q‖) := by
  have hn {w : ℂ} (hw : w.im<0) : z-w≠0 := sub_ne_zero.mpr fun e => by rw [e] at hz; linarith
  have he : pole 1 q z-pole 1 p z= -(q-p)/((z-p)*(z-q)) := by
    unfold pole; push_cast; field_simp [hn hp,hn hq]; ring
  unfold firstOrderIntegrand
  dsimp only
  rw [norm_mul,norm_mul,Complex.norm_conj,he,norm_div,norm_neg,norm_mul]
  apply (mul_le_mul_of_nonneg_left (firstOrderQ_bound hp hz) (by positivity : 0≤‖pole 1 p z‖*(‖q-p‖/(‖z-p‖*‖z-q‖)))).trans_eq
  simp [pole,norm_div,div_eq_mul_inv]; ring

theorem cross_witness_orthogonality {n j : ℕ} (p : PickSum n) (q : PickSum j)
    {W₁ W₂ : ℂ → ℂ} (ha : isWitness W₁) (hb : isWitness W₂) :
    let G := fun z => q.value z*(W₁ z-W₂ z)
    Integrable (fun z => field p.value z*conj (G z)) upperArea ∧
    (∫ z, field p.value z*conj (G z) ∂upperArea)=0 := by
  let G := fun z => q.value z*(W₁ z-W₂ z)
  have hG : DifferentiableOn ℂ G upper := q.holomorphic.mul (ha.1.sub hb.1)
  have hc : ContinuousOn G {z : ℂ | 0≤z.im} :=
    (show ContinuousOn q.value {z : ℂ | 0≤z.im} from fun z hz => (q.hasDerivAt hz).continuousAt.continuousWithinAt).mul
      (ha.2.1.sub hb.2.1)
  obtain ⟨A,hA,R,hR,h₁⟩ := ha.2.2
  obtain ⟨B,hB,T,hT,h₂⟩ := hb.2.2
  apply p.field_orthogonality hG hc (K:=q.bound*(A+B)) (T:=max 1 (max R T)) (by have := q.bound_pos; positivity)
  intro z hz hr
  have hr1 := (le_max_left 1 _).trans hr
  have hrp := zero_lt_one.trans_le hr1
  have h₁' := h₁ z hz ((le_max_left R T).trans ((le_max_right 1 _).trans hr))
  have h₂' := h₂ z hz ((le_max_right R T).trans ((le_max_right 1 _).trans hr))
  have h := norm_sub_le_norm_sub_add_norm_sub (W₁ z) ((π/2:ℝ):ℂ) (W₂ z)
  rw [norm_sub_rev ((π/2:ℝ):ℂ)] at h
  have hq := (q.global_decay hz).trans (div_le_div_of_nonneg_left q.bound_pos.le hrp (by linarith))
  change ‖q.value z*(W₁ z-W₂ z)‖≤_
  rw [norm_mul]
  exact (mul_le_mul hq (h.trans (add_le_add h₁' h₂')) (norm_nonneg _) (div_nonneg q.bound_pos.le hrp.le)).trans_eq (by ring)

/-- The first-order term splits into a density containing Q and a holomorphic
test that vanishes on pairing with the single-pole physical field. -/
theorem firstOrder_pointwise {A B W₁ W₂ : ℂ} (hA : A≠0) :
    let ι := (A.arg:ℂ)-W₁
    let v₁ := A*ι
    let v₂ := B*((B.arg:ℂ)-W₂)
    (((k₀:ℂ)*A*conj B-v₁*conj v₂).re-(v₁*conj (linearBlend A B)).re) =
      (A*conj B*firstOrderQ ι).re-(v₁*conj (B*(W₁-W₂))).re := by
  let b := B/A
  have hB : B=A*b := by dsimp [b]; field_simp [hA]
  dsimp only [linearBlend,firstOrderQ]
  change _ = _
  rw [hB,mul_div_cancel_left₀ b hA]
  simp [Complex.mul_re,Complex.mul_im,Complex.sq_norm,Complex.normSq_apply]
  ring

end Liu
