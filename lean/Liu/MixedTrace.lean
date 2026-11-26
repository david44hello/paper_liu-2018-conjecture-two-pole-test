import Liu.IsolatedStability
import Liu.EdgeLogWeight
import Liu.SmallDepthIntegral

noncomputable section
open Set Real MeasureTheory
namespace Liu

/-- The regular part paired with the shallow isolated trace. -/
def mixedTrace (s γ u x : ℝ) : ℝ :=
  (1-normalMass s)*isolatedTrace (cos γ) (sin γ+u) x + edgeRealTrace s γ u x

def mixedLogCoefficient (s γ : ℝ) : ℝ := 2*normalMass s*mixedTrace s γ 0 0

theorem mixed_trace_controls {s γ : ℝ} (hg : γ∈Icc 0 (π/2)) (hσ : 0<sin γ) :
    let a := normalMass s
    let b := 1-a
    let C := 8/(a*sin γ^4)
    let H := mixedTrace s γ
    8≤C ∧ (∀ u, 0≤u → ∀ x, |H u x|≤4*C) ∧
    (∀ x : ℝ, 0 < |x| → |x|≤1/4 → |H 0 x-H 0 0|≤5*C*|x| *(1+log (1/|x|))) ∧
    (∀ u, 0<u → u≤1/4 → ∀ x, |H u x-H 0 x|≤5*C*u*(1+log (1/u))) ∧
    |mixedLogCoefficient s γ|≤64/sin γ^4 := by
  let a := normalMass s
  let b := 1-a
  let σ := sin γ
  let C := 8/(a*σ^4)
  let H := mixedTrace s γ
  have ha : 0<a := Certificate.normalMass_pos _
  have hb : 0<b := by dsimp [a,b]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _
  have ha₁ : a≤1 := by dsimp [b] at hb; linarith
  have hb₁ : b≤1 := by dsimp [b]; linarith
  have hs₁ : σ≤1 := sin_le_one _
  have hd : 0<a*σ^4 := by positivity
  have hd₁ : a*σ^4≤1 := by
    have hh := pow_le_pow_left₀ hσ.le hs₁ 4
    norm_num at hh
    exact (mul_le_mul_of_nonneg_left hh ha.le).trans (by simpa using ha₁)
  have hC : 8≤C := by change 8≤8/(a*σ^4); rw [le_div_iff₀ hd]; linarith
  have hCs : 2/σ^2≤C := by
    apply (div_le_div_iff₀ (by positivity) hd).mpr
    have hs₂ : σ^2≤1 := by simpa using pow_le_pow_left₀ hσ.le hs₁ 2
    nlinarith only [mul_le_mul_of_nonneg_right ha₁ (pow_nonneg hσ.le 4),
      mul_le_mul_of_nonneg_right hs₂ (sq_nonneg σ),sq_nonneg σ]
  have hCs' : 1/σ≤C := by
    apply le_trans _ hCs
    rw [div_le_div_iff₀ hσ (sq_pos_of_pos hσ)]
    nlinarith [mul_le_mul_of_nonneg_left hs₁ hσ.le]
  have hsup (u : ℝ) (hu : 0≤u) (x : ℝ) : |H u x|≤4*C := by
    have hv : 0<σ+u := add_pos_of_pos_of_nonneg hσ hu
    have hI := isolatedTrace_le_depth (cos γ) x hv
    have hI₀ := isolatedTrace_nonneg (cos γ) x hv
    have hB := mul_le_mul hb₁ hI hI₀ zero_le_one
    have hc := (edge_real_trace_fixed (s:=s) hg hσ hu).2.2 x
    change |b*isolatedTrace (cos γ) (σ+u) x+edgeRealTrace s γ u x|≤4*C
    apply (abs_add_le ..).trans
    rw [abs_of_nonneg (mul_nonneg hb.le hI₀)]
    change |edgeRealTrace s γ u x|≤3*C at hc
    linarith [one_div_le_one_div_of_le hσ (by linarith : σ≤σ+u)]
  obtain ⟨hcx,hcu⟩ := edge_real_trace_moduli (s:=s) hg hσ
  have hlog {r : ℝ} (hr : 0<r) (hr₁ : r≤1/4) : 0≤log (1/r) := log_nonneg ((one_le_div hr).mpr (by linarith : r≤1))
  have combine (B B₀ c c₀ r : ℝ) (hr : 0<r) (hr₁ : r≤1/4) (hB : |B-B₀|≤C*r)
      (hc : |c-c₀|≤4*C*r*(1+log (1/r))) :
      |(B+c)-(B₀+c₀)|≤5*C*r*(1+log (1/r)) := by
    rw [show (B+c)-(B₀+c₀)=(B-B₀)+(c-c₀) by ring]
    apply (abs_add_le ..).trans ((add_le_add hB hc).trans ?_)
    nlinarith only [mul_nonneg (mul_nonneg (show 0≤C by linarith) hr.le) (hlog hr hr₁)]
  refine ⟨hC,hsup,?_,?_,?_⟩
  · intro x hx hx₁
    apply combine _ _ _ _ _ hx hx₁ _ (hcx x hx hx₁)
    simp only [add_zero,←mul_sub,abs_mul,abs_of_pos (show 0<1-normalMass s from hb)]
    have he := isolatedTrace_stability (cos γ) 0 x hσ (show 0≤(0:ℝ) from le_rfl)
    simp only [sub_zero,add_zero,mul_zero] at he
    apply (mul_le_mul hb₁ he (abs_nonneg _) zero_le_one).trans
    change 1*(|x|/(2*σ^2))≤C*|x|
    calc
      _ ≤ (2/σ^2)*|x| := by rw [one_mul]; field_simp [hσ.ne']; exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg σ)
      _ ≤ _ := mul_le_mul_of_nonneg_right hCs hx.le
  · intro u hu hu₁ x
    apply combine _ _ _ _ _ hu hu₁ _ (hcu u hu hu₁ x)
    simp only [add_zero,←mul_sub,abs_mul,abs_of_pos (show 0<1-normalMass s from hb)]
    have he := isolatedTrace_stability (cos γ) x x hσ hu.le
    simp only [sub_self,abs_zero,zero_add] at he
    apply (mul_le_mul hb₁ he (abs_nonneg _) zero_le_one).trans
    change 1*(3*u/(2*σ^2))≤C*u
    calc
      _ ≤ (2/σ^2)*u := by rw [one_mul]; field_simp [hσ.ne']; exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg σ)
      _ ≤ _ := mul_le_mul_of_nonneg_right hCs hu.le
  · change |2*a*H 0 0|≤64/σ^4
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*a)]
    apply (mul_le_mul_of_nonneg_left (hsup 0 le_rfl 0) (by positivity : 0≤2*a)).trans_eq
    dsimp [C]; field_simp [ha.ne',hσ.ne']; ring

end Liu
