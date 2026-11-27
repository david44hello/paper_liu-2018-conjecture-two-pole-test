module

public import Liu.PairedLogBounds
public import Liu.DominatedFamily

@[expose] public section

noncomputable section
open Set MeasureTheory Filter Real Complex
open scoped Topology ComplexConjugate
namespace Liu

def orientedBelow (s : Bool) (p : ℂ) := if s then p.im<0 else 0<p.im

def poleWeight (p : ℂ) : ℝ := 1+(1+‖p‖)/|p.im|

private theorem poleWeight_nonneg (p : ℂ) : 0≤poleWeight p := by unfold poleWeight; positivity

private theorem poleWeight_lower {p : ℂ} (hp : p.im<0) : poleBound 1 p=poleWeight p := by
  simp [poleWeight,poleBound,abs_of_neg hp]

private theorem poleWeight_partner (p : ℂ) : poleWeight (conj p)=poleWeight p := by simp [poleWeight]

private theorem node_log_diff (s : Bool) {w : ℂ} (h : orientedBelow (!s) w) :
    DifferentiableAt ℂ (sideLog s) w := by
  cases s
  · have hi : w.im<0 := h
    have hs : I*w∈slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simpa using hi))
    exact ((((differentiableAt_id (𝕜:=ℂ) (x:=w)).const_mul I).clog hs).sub_const _)
  · have hi : 0<w.im := h
    have hs : -I*w∈slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simpa using hi))
    exact ((((differentiableAt_id (𝕜:=ℂ) (x:=w)).const_mul (-I)).clog hs).add_const _)

theorem tailTerm_pair_diff (s : Bool) {p q : ℂ} (hp : orientedBelow s p) (hq : orientedBelow (!s) q) (x : ℝ) :
    DifferentiableAt ℂ (fun k : ℂ × ℂ => tailTerm s k.1 k.2 (x:ℂ)) (p,q) := by
  have H : orientedBelow s ((x:ℂ)-q) ∧ orientedBelow s (p-q) ∧
      orientedBelow (!s) ((x:ℂ)-p) ∧ orientedBelow (!s) (q-p) := by
    cases s <;> simp_all [orientedBelow] <;> linarith
  have n (r : ℂ) (hr : r.im≠0) : (x:ℂ)-r ≠ 0 := by
    intro e; apply hr; simpa using (congrArg Complex.im (sub_eq_zero.mp e)).symm
  have hn (k : Bool) (r : ℂ) (hr : orientedBelow k r) : r.im≠0 := by
    cases k
    · exact (show 0<r.im from hr).ne'
    · exact (show r.im<0 from hr).ne
  have hn₁ := n p (hn s p hp)
  have hn₂ := n q (hn (!s) q hq)
  have h₁ := node_log_diff (!s) (w:=(x:ℂ)-q) (by simpa using H.1)
  have h₂ := node_log_diff (!s) (w:=p-q) (by simpa using H.2.1)
  have h₃ := node_log_diff s H.2.2.1
  have h₄ := node_log_diff s H.2.2.2
  unfold tailTerm
  fun_prop (disch := assumption)

theorem moving_term_dominated {U : Set ℂ} (hU : IsOpen U) (s : Bool) {p q : ℂ → ℂ}
    (dp : DifferentiableOn ℂ p U) (dq : DifferentiableOn ℂ q U)
    (hp : ∀ t∈U, orientedBelow s (p t)) (hq : ∀ t∈U, orientedBelow (!s) (q t)) :
    DominatedFamily 2 U (fun t x => tailTerm s (p t) (q t) (x:ℂ)) := by
  refine ⟨fun t => ?_,fun x t ht => ?_,?_⟩
  · cases s <;> unfold tailTerm sideLog <;> simp only [Bool.not_true,Bool.not_false,Bool.false_eq_true,if_false,if_true]
    all_goals unfold lowerNodeLog upperNodeLog; fun_prop
  · exact ((tailTerm_pair_diff s (hp _ ht) (hq _ ht) x).comp t
      ((dp.differentiableAt (hU.mem_nhds ht)).prodMk (dq.differentiableAt (hU.mem_nhds ht)))).differentiableWithinAt
  · intro t ht
    let B := fun w => 2*(poleWeight (p w)*poleWeight (q w))
    have ne (k : Bool) (r : ℂ) (hr : orientedBelow k r) : |r.im|≠0 := by
      cases k
      · exact abs_ne_zero.mpr (show 0<r.im from hr).ne'
      · exact abs_ne_zero.mpr (show r.im<0 from hr).ne
    have hpn := ne _ _ (hp t ht)
    have hqn := ne _ _ (hq t ht)
    have hpc := (dp.differentiableAt (hU.mem_nhds ht)).continuousAt
    have hqc := (dq.differentiableAt (hU.mem_nhds ht)).continuousAt
    have hBc : ContinuousAt B t := by dsimp [B,poleWeight]; fun_prop (disch := assumption)
    have hK : ∀ᶠ w in 𝓝 t, B w<B t+1 := hBc.eventually_lt continuousAt_const (by linarith)
    refine ⟨fun x => (B t+1)*isolatedTrace 0 1 x,(isolatedTrace_memLp 0 zero_lt_one).const_smul (B t+1),?_⟩
    filter_upwards [hK,hU.mem_nhds ht] with w hw hmem x
    apply (le_trans _ (mul_le_mul_of_nonneg_right hw.le (isolatedTrace_nonneg _ _ zero_lt_one)))
    cases s
    · have l : (q w).im<0 := hq w hmem
      have r : 0<(p w).im := hp w hmem
      have h := (separated_term_bounds l r x).2
      simpa only [B,poleWeight_lower l,poleWeight_lower (p:=(conj (p w))) (by simpa using r),poleWeight_partner] using h
    · have l : (p w).im<0 := hp w hmem
      have r : 0<(q w).im := hq w hmem
      have h := (separated_term_bounds l r x).1
      simpa only [B,poleWeight_lower l,poleWeight_lower (p:=(conj (q w))) (by simpa using r),poleWeight_partner] using h

end Liu
