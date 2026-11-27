module

public import Liu.BlendExpansion
public import Liu.ClusterDensity

@[expose] public section

noncomputable section
open Set Real MeasureTheory
open scoped ComplexConjugate Topology
namespace Liu

def blendWitness (A B W₁ W₂ : ℂ → ℂ) (z : ℂ) :=
  (A z*W₁ z+B z*W₂ z)/(A z+B z)

theorem blendWitness_isWitness {n j k : ℕ} (p : PickSum n) (q : PickSum j) (s : PickSum k)
    (hs : s.value=p.value+q.value) {W₁ W₂ : ℂ → ℂ} (h₁ : isWitness W₁) (h₂ : isWitness W₂) :
    isWitness (blendWitness p.value q.value W₁ W₂) := by
  have he (z : ℂ) : s.value z=p.value z+q.value z := congrFun hs z
  have hn (z : ℂ) (hz : 0≤z.im) : p.value z+q.value z≠0 := by
    rw [←he]; intro h; have hh := s.value_im_pos hz; simp [h] at hh
  have hP : ContinuousOn p.value {z : ℂ | 0≤z.im} := fun _ hz => (p.hasDerivAt hz).continuousAt.continuousWithinAt
  have hQ : ContinuousOn q.value {z : ℂ | 0≤z.im} := fun _ hz => (q.hasDerivAt hz).continuousAt.continuousWithinAt
  refine ⟨((p.holomorphic.mul h₁.1).add (q.holomorphic.mul h₂.1)).div (p.holomorphic.add q.holomorphic)
    (fun z hz => hn z (le_of_lt hz)),((hP.mul h₁.2.1).add (hQ.mul h₂.2.1)).div (hP.add hQ) hn,?_⟩
  obtain ⟨c,hc,hc'⟩ := s.two_sided_decay
  obtain ⟨a,ha,R,hR,h₁a⟩ := h₁.2.2
  obtain ⟨b,hb,T,hT,h₂b⟩ := h₂.2.2
  have hp := p.bound_pos
  have hq := q.bound_pos
  refine ⟨(p.bound*a+q.bound*b)/c,by positivity,max 1 (max R T),lt_of_lt_of_le zero_lt_one (le_max_left ..),?_⟩
  intro z hz hr
  let r := ‖z‖
  have hr1 : 1≤r := (le_max_left 1 _).trans hr
  have hrp := zero_lt_one.trans_le hr1
  have hR' := (le_max_left R T).trans ((le_max_right 1 _).trans hr)
  have hT' := (le_max_right R T).trans ((le_max_right 1 _).trans hr)
  have hform : blendWitness p.value q.value W₁ W₂ z-((π/2:ℝ):ℂ) =
      (p.value z*(W₁ z-((π/2:ℝ):ℂ))+q.value z*(W₂ z-((π/2:ℝ):ℂ)))/s.value z := by
    rw [he]; unfold blendWitness; field_simp [hn z hz]; ring
  have h₁n := mul_le_mul (p.global_decay hz) (h₁a z hz hR') (norm_nonneg _) (by positivity)
  have h₂n := mul_le_mul (q.global_decay hz) (h₂b z hz hT') (norm_nonneg _) (by positivity)
  rw [hform,norm_div]
  have hlog : 0≤1+log r := by linarith [log_nonneg hr1]
  have hg : 0<1+r := by positivity
  have hbnd := (norm_add_le (p.value z*(W₁ z-((π/2:ℝ):ℂ))) (q.value z*(W₂ z-((π/2:ℝ):ℂ)))).trans
    (by simpa only [norm_mul] using add_le_add h₁n h₂n)
  apply (div_le_div₀ ((norm_nonneg _).trans hbnd) hbnd (div_pos hc hg) (hc' z hz).1).trans_eq
  dsimp only [r] at *
  field_simp [hc.ne',hg.ne',hrp.ne'] <;> ring

end Liu
