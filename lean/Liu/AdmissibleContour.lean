module

public import Liu.ContourFTC
public import Liu.SlitHolomorphic
public import Liu.ContourMajorant

@[expose] public section

noncomputable section
open Set MeasureTheory Real Complex Filter Metric
open scoped Topology
namespace Liu

/-- A real-line contour parametrized by a locally absolutely continuous
curve that agrees with the identity outside a compact interval. -/
structure RealContour where
  path : ℝ → ℂ
  ac : ∀ a b, AbsolutelyContinuousOnInterval path a b
  tail : ∃ R>0, ∀ x : ℝ, R≤|x| → path x=(x:ℂ)

def RealContour.admissible (γ : RealContour) (P Q : Fin 3 → ℂ) := ∀ x, γ.path x∈offCuts P Q

def RealContour.integral (γ : RealContour) (f : ℂ → ℂ) : ℂ := ∫ x : ℝ, f (γ.path x)*deriv γ.path x

theorem RealContour.continuous (γ : RealContour) : Continuous γ.path := by
  rw [continuous_iff_continuousAt]
  intro x
  apply (γ.ac (x-1) (x+1)).continuousOn.continuousAt
  rw [uIcc_of_le (by linarith)]; exact Icc_mem_nhds (by linarith) (by linarith)

theorem RealContour.tail_with_deriv (γ : RealContour) :
    ∃ R>0, ∀ x : ℝ, R≤|x| → γ.path x=(x:ℂ) ∧ deriv γ.path x=1 := by
  obtain ⟨R,hR,ht⟩ := γ.tail
  refine ⟨R+1,by linarith,fun x hx => ⟨ht x (by linarith),?_⟩⟩
  have hnear : ∀ᶠ t : ℝ in 𝓝 x, R < |t| := continuousAt_const.eventually_lt continuous_abs.continuousAt (by linarith)
  have eq : γ.path =ᶠ[𝓝 x] (fun t : ℝ => (t:ℂ)) := hnear.mono fun t ht' => ht t ht'.le
  exact (Complex.ofRealCLM.hasDerivAt.congr_of_eventuallyEq eq).deriv

theorem RealContour.exists_admissible (P Q : Fin 3 → ℂ) (h : ∀ i j, ¬rayCollision (P i) (Q j)) :
    ∃ γ : RealContour, γ.admissible P Q := by
  obtain ⟨g,hg,hm,ht⟩ := admissible_graph_exists P Q h
  exact ⟨⟨g,fun a b => hg.contDiffOn.absolutelyContinuousOnInterval,ht⟩,hm⟩

def straightContour : RealContour where
  path := (fun t : ℝ => (t:ℂ))
  ac := fun a b => (show ContDiffOn ℝ 1 (fun t : ℝ => (t:ℂ)) (uIcc a b) from Complex.ofRealCLM.contDiff.contDiffOn).absolutelyContinuousOnInterval
  tail := ⟨1,zero_lt_one,fun _ _ => rfl⟩

/-- Parameters, nodes and partners on an open set free of opposite vertical
collisions. The path itself may pass to either side of the real line. -/
structure WindowFamily (U : Set ℂ) where
  lower : Fin 3 → ℂ → ℂ
  partner : Fin 3 → ℂ → ℂ
  mass₁ : ℂ → ℂ
  mass₂ : ℂ → ℂ
  openSet : IsOpen U
  dl : ∀ i, DifferentiableOn ℂ (lower i) U
  dq : ∀ i, DifferentiableOn ℂ (partner i) U
  da : DifferentiableOn ℂ mass₁ U
  db : DifferentiableOn ℂ mass₂ U
  clear : ∀ w∈U, ∀ i j, ¬rayCollision (lower i w) (partner j w)

def WindowFamily.L {U} (W : WindowFamily U) (w : ℂ) := fun i => W.lower i w
def WindowFamily.Q {U} (W : WindowFamily U) (w : ℂ) := fun i => W.partner i w
def WindowFamily.H {U} (W : WindowFamily U) (w z : ℂ) := totalDensity (W.L w) (W.Q w) (W.mass₁ w) (W.mass₂ w) z
def WindowFamily.pathDomain {U} (W : WindowFamily U) (γ : RealContour) :=
  {w | w∈U ∧ γ.admissible (W.L w) (W.Q w)}

theorem WindowFamily.joint_diff {U} (W : WindowFamily U) {w z : ℂ} (hw : w∈U) (hz : z∈offCuts (W.L w) (W.Q w)) :
    DifferentiableAt ℂ (fun k : ℂ × ℂ => W.H k.1 k.2) (w,z) := by
  have hd {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) : DifferentiableAt ℂ (fun k : ℂ × ℂ => f k.1) (w,z) :=
    (hf.differentiableAt (W.openSet.mem_nhds hw)).comp (w,z) differentiableAt_fst
  exact totalDensity_diff_pull (fun i => hd (W.dl i)) (fun j => hd (W.dq j))
    (hd W.da) (hd W.db) differentiableAt_snd hz (W.clear w hw)

theorem WindowFamily.shape_bound {U} (W : WindowFamily U) {K : Set ℂ} (hK : IsCompact K) (hsub : K⊆U) :
    ∃ B>0, ∀ w∈K, ‖W.mass₁ w‖+‖W.mass₂ w‖≤B ∧ (∀ i, ‖W.lower i w‖≤B) ∧
      (∀ i, ‖W.partner i w‖≤B) ∧ totalLogCost (W.L w) (W.Q w)≤B := by
  let M := fun w => ‖W.mass₁ w‖+‖W.mass₂ w‖+(∑ i,‖W.lower i w‖)+(∑ i,‖W.partner i w‖)+totalLogCost (W.L w) (W.Q w)
  have cost (w : ℂ) (hw : w∈U) : ContinuousAt (fun v => totalLogCost (W.L v) (W.Q v)) w := by
    have l (i : Fin 3) := W.dl i |>.differentiableAt (W.openSet.mem_nhds hw)
    have q (j : Fin 3) := W.dq j |>.differentiableAt (W.openSet.mem_nhds hw)
    have cd (i j : Fin 3) := (clearance_iff ..).mp (W.clear w hw i j)
    have T (i j : Fin 3) : ContinuousAt (fun t => sideLog false (W.lower i t-W.partner j t)) w := by
      have hc := (sideLog_diff_on_cut_complement (cd i j).1).continuousAt
      exact hc.tendsto.comp ((l i).continuousAt.tendsto.sub (q j).continuousAt.tendsto)
    have T' (i j : Fin 3) : ContinuousAt (fun t => sideLog true (W.partner j t-W.lower i t)) w := by
      have hc := (sideLog_diff_on_cut_complement (cd i j).2).continuousAt
      exact hc.tendsto.comp ((q j).continuousAt.tendsto.sub (l i).continuousAt.tendsto)
    have finite {ι : Type} [Fintype ι] (g : ι → ℂ → ℝ) (hg : ∀ i, ContinuousAt (g i) w) :
        ContinuousAt (fun v => ∑ i,g i v) w := by fun_prop
    apply ContinuousAt.add
    · apply finite; intro i; apply finite; intro j
      exact (T i.castSucc j).norm.add (T' i.castSucc j).norm
    · apply finite; intro i; apply finite; intro j
      exact (T' j i.castSucc).norm.add (T j i.castSucc).norm
  have hM : ContinuousOn M K := by
    intro w hw; apply ContinuousAt.continuousWithinAt
    have hm := (W.da.differentiableAt (W.openSet.mem_nhds (hsub hw))).continuousAt
    have hn := (W.db.differentiableAt (W.openSet.mem_nhds (hsub hw))).continuousAt
    have l (i : Fin 3) := (W.dl i).differentiableAt (W.openSet.mem_nhds (hsub hw)) |>.continuousAt
    have q (i : Fin 3) := (W.dq i).differentiableAt (W.openSet.mem_nhds (hsub hw)) |>.continuousAt
    have hcost := cost w (hsub hw)
    unfold M; fun_prop
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hM
  refine ⟨|B|+1,by positivity,fun w hw => ?_⟩
  have c₀ : 0≤totalLogCost (W.L w) (W.Q w) := add_nonneg (sideLogCost_nonneg ..) (sideLogCost_nonneg ..)
  have m := (le_abs_self (M w)).trans (hB w hw)
  dsimp only [M] at m
  have hl : 0≤∑ i,‖W.lower i w‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hq : 0≤∑ i,‖W.partner i w‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨by linarith [le_abs_self B],fun i => ?_,fun i => ?_,by linarith [le_abs_self B,norm_nonneg (W.mass₁ w),norm_nonneg (W.mass₂ w)]⟩
  · linarith [Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) => norm_nonneg (W.lower j w)) (Finset.mem_univ i),le_abs_self B,norm_nonneg (W.mass₁ w),norm_nonneg (W.mass₂ w)]
  · linarith [Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 3))) => norm_nonneg (W.partner j w)) (Finset.mem_univ i),le_abs_self B,norm_nonneg (W.mass₁ w),norm_nonneg (W.mass₂ w)]

end Liu
