module

public import Liu.SlitPrimitives
public import Liu.CutSeparation

@[expose] public section

noncomputable section
open Set Filter Real Complex
open scoped Topology
namespace Liu

def cutHeights (P Q : Fin 3 → ℂ) (x : ℝ) : Set ℝ :=
  {y | (∀ i, x=(P i).re → (P i).im < y) ∧ (∀ j, x=(Q j).re → y < (Q j).im)}

def cutAbscissas (P Q : Fin 3 → ℂ) : Finset ℝ :=
  Finset.univ.image (fun i => (P i).re) ∪ Finset.univ.image (fun j => (Q j).re)

def offCuts (P Q : Fin 3 → ℂ) : Set ℂ := {z | z.im∈cutHeights P Q z.re}

theorem cutHeights_regular (P Q : Fin 3 → ℂ) (x : ℝ) :
    IsOpen (cutHeights P Q x) ∧ Convex ℝ (cutHeights P Q x) := by
  classical
  let A := fun i : Fin 3 => if x=(P i).re then Ioi (P i).im else univ
  let B := fun j : Fin 3 => if x=(Q j).re then Iio (Q j).im else univ
  have e : cutHeights P Q x=(⋂ i,A i)∩(⋂ j,B j) := by
    ext y; simp only [cutHeights,mem_setOf_eq,mem_inter_iff,mem_iInter]
    apply and_congr <;> apply forall_congr' <;> intro i
    · by_cases h : x=(P i).re <;> simp [A,h]
    · by_cases h : x=(Q i).re <;> simp [B,h]
  rw [e]
  constructor
  · apply IsOpen.inter <;> apply isOpen_iInter_of_finite <;> intro i
    · dsimp [A]; split <;> simp [isOpen_Ioi]
    · dsimp [B]; split <;> simp [isOpen_Iio]
  · apply Convex.inter <;> apply convex_iInter <;> intro i
    · dsimp [A]; split <;> first | exact convex_Ioi _ | exact convex_univ
    · dsimp [B]; split <;> first | exact convex_Iio _ | exact convex_univ

theorem cutHeights_nonempty (P Q : Fin 3 → ℂ) (h : ∀ i j, ¬rayCollision (P i) (Q j)) (x : ℝ) :
    (cutHeights P Q x).Nonempty := by
  classical
  let L := (Finset.univ.filter (fun i => x=(P i).re)).image (fun i => (P i).im)
  let R := (Finset.univ.filter (fun j => x=(Q j).re)).image (fun j => (Q j).im)
  have mL {i : Fin 3} (e : x=(P i).re) : (P i).im∈L := Finset.mem_image.mpr ⟨i,by simp [e],rfl⟩
  have mR {i : Fin 3} (e : x=(Q i).re) : (Q i).im∈R := Finset.mem_image.mpr ⟨i,by simp [e],rfl⟩
  have H {u v : ℝ} (hu : u∈L) (hv : v∈R) : u < v := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
    exact lt_of_not_ge fun e => h i j ⟨(Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2,e⟩
  by_cases l : L.Nonempty
  · by_cases r : R.Nonempty
    · have hh := H (L.max'_mem l) (R.min'_mem r)
      refine ⟨(L.max' l+R.min' r)/2,fun i e => ?_,fun j e => ?_⟩
      · linarith [L.le_max' _ (mL e)]
      · linarith [R.min'_le _ (mR e)]
    · exact ⟨L.max' l+1,fun i e => by linarith [L.le_max' _ (mL e)],fun j e => False.elim (r ⟨_,mR e⟩)⟩
  · by_cases r : R.Nonempty
    · exact ⟨R.min' r-1,fun i e => False.elim (l ⟨_,mL e⟩),fun j e => by linarith [R.min'_le _ (mR e)]⟩
    · exact ⟨0,fun i e => False.elim (l ⟨_,mL e⟩),fun j e => False.elim (r ⟨_,mR e⟩)⟩

theorem offCuts_primitives (P Q : Fin 3 → ℂ) :
    IsOpen (offCuts P Q) ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (offCuts P Q) → IsExactOn f (offCuts P Q) := by
  have he : slitDomain univ (cutAbscissas P Q) (cutHeights P Q)=offCuts P Q := by
    ext z
    change (z.re∈(univ : Set ℝ) ∧ (z.re∈cutAbscissas P Q → _)) ↔ _
    simp only [mem_univ,true_and]
    constructor
    · intro ht
      exact ⟨fun i e => (ht (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩))).1 i e,
        fun j e => (ht (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e.symm⟩))).2 j e⟩
    · exact fun hz _ => hz
  rw [←he]
  exact slit_domain_exact _ _ (fun x => (cutHeights_regular P Q x).1) (fun x => (cutHeights_regular P Q x).2)
    univ isOpen_univ convex_univ

/-- A smooth graph through the gaps, equal to the real line on both tails. -/
theorem admissible_graph_exists (P Q : Fin 3 → ℂ) (h : ∀ i j, ¬rayCollision (P i) (Q j)) :
    ∃ γ : ℝ → ℂ, ContDiff ℝ 1 γ ∧ (∀ t : ℝ, γ t∈offCuts P Q) ∧
      ∃ R > 0, ∀ t : ℝ, R ≤ |t| → γ t=(t:ℂ) := by
  classical
  let S := cutAbscissas P Q
  choose y hy using cutHeights_nonempty P Q h
  let G : Polynomial ℝ := Lagrange.interpolate S id y
  let R := 1+∑ x∈S,|x|
  have hR : 0 < R := by dsimp [R]; positivity
  let b : ContDiffBump (0:ℝ) := ⟨R,R+1,hR,by linarith⟩
  let γ := fun t : ℝ => (t:ℂ)+((b t*G.eval t:ℝ):ℂ)*I
  have eq (x : ℝ) (hx : x∈S) : b x*G.eval x=y x := by
    have hle : |x| ≤ R := by dsimp [R]; linarith [Finset.single_le_sum (fun j (_ : j∈S) => abs_nonneg j) hx]
    have hb : b x=1 := b.one_of_mem_closedBall (by simpa [Real.dist_eq,b] using hle)
    rw [hb,one_mul]; exact Lagrange.eval_interpolate_at_node _ Function.injective_id.injOn hx
  refine ⟨γ,?_,?_,R+1,by linarith,?_⟩
  · have hf : ContDiff ℝ 1 (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff
    have hg : ContDiff ℝ 1 (fun t => G.eval t) := by simpa using G.contDiff_aeval (𝕜:=ℝ) 1
    exact hf.add ((hf.comp (b.contDiff.mul hg)).mul contDiff_const)
  · intro t
    change (γ t).im∈cutHeights P Q (γ t).re
    simp only [γ,Complex.add_re,Complex.add_im,Complex.ofReal_im,Complex.ofReal_re,Complex.mul_I_re,Complex.mul_I_im,neg_zero,add_zero,zero_add]
    by_cases ht : t∈S
    · rw [eq _ ht]; exact hy t
    · exact ⟨fun i e => False.elim (ht (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩))),
        fun j e => False.elim (ht (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e.symm⟩)))⟩
  · intro t ht
    have hb : b t=0 := b.zero_of_le_dist (by simpa [b,Real.dist_eq] using ht)
    simp [γ,hb]

end Liu
