import Liu.OnePoleBounds
import Liu.Blend

noncomputable section
open Set Real
namespace Liu

def Pair.massFraction (p : Pair) := p.a₁/p.mass

def Pair.massCentre (p : Pair) : ℂ :=
  p.w₂ + (p.massFraction:ℂ)*(p.w₁-p.w₂)

def Pair.separation (p : Pair) := ‖p.w₁-p.w₂‖

def Pair.clusterError (p : Pair) (z : ℂ) :=
  ((p.massFraction*(1-p.massFraction):ℝ):ℂ)*(p.w₁-p.w₂)^2/((z-p.w₁)*(z-p.w₂))

theorem Pair.massFraction_range (p : Pair) : p.massFraction∈Ioo 0 1 := by
  refine ⟨div_pos p.ha₁ p.mass_pos,(div_lt_one p.mass_pos).mpr ?_⟩
  dsimp [Pair.mass]; linarith [p.ha₂]

theorem Pair.massCentre_below (p : Pair) : p.massCentre.im<0 := by
  have hh := p.massFraction_range
  have hm : p.massCentre.im=p.massFraction*p.w₁.im+(1-p.massFraction)*p.w₂.im := by
    simp [Pair.massCentre,Complex.mul_im]; ring
  rw [hm]
  exact add_neg (mul_neg_of_pos_of_neg hh.1 p.hw₁) (mul_neg_of_pos_of_neg (sub_pos.mpr hh.2) p.hw₂)

theorem Pair.value_cluster_factor (p : Pair) {z : ℂ} (hz : 0≤z.im) :
    p.value z=pole p.mass p.massCentre z*(1+p.clusterError z) := by
  have hn {w : ℂ} (hw : w.im<0) : z-w≠0 := sub_ne_zero.mpr fun e => by rw [e] at hz; linarith
  have ha : (p.a₁:ℂ)=(p.massFraction:ℂ)*(p.mass:ℂ) := by
    exact_mod_cast (div_mul_cancel₀ p.a₁ p.mass_pos.ne').symm
  have hb : (p.a₂:ℂ)=(1-(p.massFraction:ℂ))*(p.mass:ℂ) := by
    rw [sub_mul,one_mul,←ha]; simp [Pair.mass]
  dsimp only [Pair.value,pole,Pair.clusterError]
  push_cast
  field_simp [hn p.hw₁,hn p.hw₂,hn p.massCentre_below]
  rw [ha,hb]
  dsimp only [Pair.massCentre]; ring

/-- Uniform second-order control from cancellation at the mass centre. -/
theorem Pair.clusterError_bound (p : Pair) (hd : p.separation≤ -p.massCentre.im/4)
    {z : ℂ} (hz : 0≤z.im) :
    ‖p.clusterError z‖≤2*(p.massFraction*(1-p.massFraction))*p.separation^2/‖z-p.massCentre‖^2 ∧
    ‖p.clusterError z‖≤1/8 := by
  let μ := p.massFraction
  let d := p.separation
  let r := ‖z-p.massCentre‖
  have hμ := p.massFraction_range
  have hν : 0≤1-μ := sub_nonneg.mpr hμ.2.le
  have hA : 0≤μ*(1-μ) := mul_nonneg hμ.1.le hν
  have hd0 : 0≤d := norm_nonneg _
  have hu : -p.massCentre.im ≤ r := by
    apply le_trans _ (Complex.im_le_norm _); rw [Complex.sub_im]; linarith
  have hr : 0<r := (neg_pos.mpr p.massCentre_below).trans_le hu
  have hdist : d≤r/4 := by linarith
  have h₁ : ‖p.w₁-p.massCentre‖≤d := by
    rw [show p.w₁-p.massCentre=(1-(μ:ℂ))*(p.w₁-p.w₂) by dsimp [Pair.massCentre,μ]; ring,
      norm_mul,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_of_nonneg hν]
    exact mul_le_of_le_one_left hd0 (by linarith [show 0≤μ from hμ.1.le])
  have h₂ : ‖p.w₂-p.massCentre‖≤d := by
    rw [show p.w₂-p.massCentre= -(μ:ℂ)*(p.w₁-p.w₂) by dsimp [Pair.massCentre,μ]; ring,
      norm_mul,norm_neg,Complex.norm_of_nonneg hμ.1.le]
    exact mul_le_of_le_one_left hd0 hμ.2.le
  have hL {w : ℂ} (hw : ‖w-p.massCentre‖≤d) : 3*r/4 ≤ ‖z-w‖ := by
    have hh := norm_sub_le_norm_sub_add_norm_sub z w p.massCentre
    change r≤_ at hh; linarith
  have hprod := mul_le_mul (hL h₁) (hL h₂) (by positivity : 0≤3*r/4) (norm_nonneg _)
  have hp : 0<‖z-p.w₁‖*‖z-p.w₂‖ := (mul_pos (by positivity : 0<3*r/4) (by positivity : 0<3*r/4)).trans_le hprod
  have he : ‖p.clusterError z‖=μ*(1-μ)*d^2/(‖z-p.w₁‖*‖z-p.w₂‖) := by
    simp only [Pair.clusterError,norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hμ.1.le,abs_of_nonneg (show 0≤1-p.massFraction from hν)]; rfl
  have hb : ‖p.clusterError z‖≤2*(μ*(1-μ))*d^2/r^2 := by
    rw [he,div_le_div_iff₀ hp (sq_pos_of_pos hr)]
    have hlow : r^2≤2*(‖z-p.w₁‖*‖z-p.w₂‖) := by nlinarith [sq_nonneg r]
    nlinarith only [mul_le_mul_of_nonneg_left hlow (mul_nonneg hA (sq_nonneg d))]
  refine ⟨hb,hb.trans ((div_le_iff₀ (sq_pos_of_pos hr)).mpr ?_)⟩
  have ha1 : μ*(1-μ)≤1 := by nlinarith [sq_nonneg μ,show μ≤1 from hμ.2.le]
  have hd2 := pow_le_pow_left₀ hd0 hdist 2
  nlinarith only [hd2,mul_le_mul_of_nonneg_right ha1 (sq_nonneg d)]

end Liu
