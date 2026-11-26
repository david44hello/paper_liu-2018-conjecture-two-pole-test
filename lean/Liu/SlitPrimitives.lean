import Mathlib

noncomputable section
open Set Filter Complex
open scoped Topology
namespace Liu

/-- Vertically cut domain. At each exceptional abscissa the allowed heights
form an open interval. Outside the exceptional fibres every height is allowed. -/
def slitDomain (J : Set ℝ) (S : Finset ℝ) (A : ℝ → Set ℝ) : Set ℂ :=
  {z | z.re∈J ∧ (z.re∈S → z.im∈A z.re)}

private theorem exact_convex {U : Set ℂ} (ho : IsOpen U) (hc : Convex ℝ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) : IsExactOn f U := by
  obtain ⟨g,hg⟩ := hc.exists_forall_hasDerivWithinAt hf
  exact ⟨g,fun z hz => (hg z hz).hasDerivAt (ho.mem_nhds hz)⟩

private theorem exact_union {U V : Set ℂ} (hu : IsOpen U) (hv : IsOpen V) (hc : IsPreconnected (U∩V))
    {f : ℂ → ℂ} (h : IsExactOn f U) (k : IsExactOn f V) : IsExactOn f (U∪V) := by
  classical
  obtain ⟨g,hg⟩ := h
  obtain ⟨j,hj⟩ := k
  obtain ⟨c,he⟩ := (hu.inter hv).exists_eq_add_of_deriv_eq hc
    (fun z hz => (hg z hz.1).differentiableAt.differentiableWithinAt)
    (fun z hz => (hj z hz.2).differentiableAt.differentiableWithinAt)
    (fun z hz => (hg z hz.1).deriv.trans (hj z hz.2).deriv.symm)
  refine ⟨fun z => if z∈U then g z else j z+c,?_⟩
  intro z hz
  rcases hz with hU|hV
  · apply (hg z hU).congr_of_eventuallyEq
    filter_upwards [hu.mem_nhds hU] with w hw
    simp [hw]
  · apply ((hj z hV).add_const c).congr_of_eventuallyEq
    filter_upwards [hv.mem_nhds hV] with w hw
    by_cases h : w∈U
    · simpa only [if_pos h] using he (show w∈U∩V from ⟨h,hw⟩)
    · simp [h]

private theorem one_fibre_exact (J : Set ℝ) (m : ℝ) (A : ℝ → Set ℝ)
    (hJ : IsOpen J) (cJ : Convex ℝ J) (hA : IsOpen (A m)) (cA : Convex ℝ (A m)) :
    IsOpen (slitDomain J {m} A) ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (slitDomain J {m} A) →
      IsExactOn f (slitDomain J {m} A) := by
  let B := Complex.re ⁻¹' J
  let L := B ∩ {z : ℂ | z.re < m}
  let R := B ∩ {z : ℂ | m < z.re}
  let H := B ∩ Complex.im ⁻¹' A m
  have oB : IsOpen B := hJ.preimage continuous_re
  have cB : Convex ℝ B := cJ.linear_preimage reCLM.toLinearMap
  have oL : IsOpen L := oB.inter (isOpen_lt continuous_re continuous_const)
  have oR : IsOpen R := oB.inter (isOpen_lt continuous_const continuous_re)
  have oH : IsOpen H := oB.inter (hA.preimage continuous_im)
  have cL : Convex ℝ L := cB.inter (convex_halfSpace_re_lt m)
  have cR : Convex ℝ R := cB.inter (convex_halfSpace_re_gt m)
  have cH : Convex ℝ H := cB.inter (cA.linear_preimage imCLM.toLinearMap)
  have he : slitDomain J {m} A=(L∪H)∪R := by
    ext z; simp only [slitDomain,L,H,R,B,mem_setOf_eq,Finset.mem_singleton,mem_inter_iff,mem_union,mem_preimage]
    by_cases e : z.re=m
    · simp [e]
    · rcases lt_or_gt_of_ne e with h|h <;> simp [e,h] <;> tauto
  have inter : (L∪H)∩R=H∩R := by
    ext z; change ((z∈L ∨ z∈H) ∧ z∈R) ↔ (z∈H ∧ z∈R)
    have dis : z∈L → z∈R → False := fun hl hr => (not_lt_of_ge (show z.re < m from hl.2).le) (show m < z.re from hr.2)
    tauto
  rw [he]
  refine ⟨(oL.union oH).union oR,fun f hf => ?_⟩
  have hlh := hf.mono (subset_union_left (s:=L∪H) (t:=R))
  have left := exact_union oL oH (cL.inter cH).isPreconnected
    (exact_convex oL cL (hlh.mono subset_union_left)) (exact_convex oH cH (hlh.mono subset_union_right))
  apply exact_union (oL.union oH) oR _ left (exact_convex oR cR (hf.mono subset_union_right))
  rw [inter]; exact (cH.inter cR).isPreconnected

/-- A holomorphic function on the complement of finitely many vertical
half-rays has a single-valued primitive when the allowed fibres are open
intervals. The proof glues convex strips across connected overlaps. -/
theorem slit_domain_exact (S : Finset ℝ) (A : ℝ → Set ℝ)
    (hA : ∀ x, IsOpen (A x)) (cA : ∀ x, Convex ℝ (A x)) (J : Set ℝ) (hJ : IsOpen J) (cJ : Convex ℝ J) :
    IsOpen (slitDomain J S A) ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (slitDomain J S A) →
      IsExactOn f (slitDomain J S A) := by
  classical
  induction S using Finset.induction_on_min generalizing J with
  | empty =>
    have he : slitDomain J ∅ A=Complex.re ⁻¹' J := by ext; simp [slitDomain]
    rw [he]
    exact ⟨hJ.preimage continuous_re,fun f hf => exact_convex (hJ.preimage continuous_re) (cJ.linear_preimage reCLM.toLinearMap) hf⟩
  | insert m S hmin ih =>
    by_cases hne : S.Nonempty
    · let n := S.min' hne
      have hmn : m < n := hmin n (S.min'_mem hne)
      let l := (2*m+n)/3
      let r := (m+2*n)/3
      have hml : m < l := by dsimp [l]; linarith
      have hlr : l < r := by dsimp [l,r]; linarith
      have hrn : r < n := by dsimp [r]; linarith
      let L := slitDomain (J∩Iio r) {m} A
      let R := slitDomain (J∩Ioi l) S A
      have hL := one_fibre_exact (J∩Iio r) m A (hJ.inter isOpen_Iio) (cJ.inter (convex_Iio _)) (hA m) (cA m)
      have hR := ih (J∩Ioi l) (hJ.inter isOpen_Ioi) (cJ.inter (convex_Ioi _))
      have before (x : ℝ) (hx : x < r) : x∉S := fun he => (not_lt_of_ge (S.min'_le x he)) (hx.trans hrn)
      have both : slitDomain J (insert m S) A = L∪R := by
        ext z
        change (z.re∈J ∧ (z.re∈insert m S → _)) ↔ (_ ∨ _)
        simp only [L,R,slitDomain,mem_setOf_eq,Finset.mem_insert,Finset.mem_singleton,mem_inter_iff,mem_Iio,mem_Ioi]
        by_cases h : z.re < r
        · have e := before z.re h
          by_cases hl : l < z.re
          · have en : z.re≠m := (hml.trans hl).ne'; simp [e,en,h,hl]
          · simp [e,h,hl]
        · have hl := hlr.trans_le (le_of_not_gt h)
          have en : z.re≠m := (hml.trans hl).ne'
          simp [h,hl,en]
      have overlap : L∩R = Complex.re ⁻¹' (J ∩ Ioo l r) := by
        ext z
        change (((z.re∈J∩Iio r) ∧ (z.re∈({m}:Finset ℝ) → _)) ∧
          ((z.re∈J∩Ioi l) ∧ (z.re∈S → _))) ↔ _
        constructor
        · rintro ⟨⟨⟨hz,hr⟩,_⟩,⟨⟨_,hl⟩,_⟩⟩; exact ⟨hz,hl,hr⟩
        · rintro ⟨hz,hl,hr⟩
          exact ⟨⟨⟨hz,hr⟩,fun e => False.elim ((hml.trans hl).ne' (Finset.mem_singleton.mp e))⟩,
            ⟨⟨hz,hl⟩,fun e => False.elim (before _ hr e)⟩⟩
      rw [both]
      refine ⟨hL.1.union hR.1,fun f hf => exact_union hL.1 hR.1 ?_ (hL.2 f (hf.mono subset_union_left))
        (hR.2 f (hf.mono subset_union_right))⟩
      rw [overlap]; exact ((cJ.inter (convex_Ioo _ _)).linear_preimage reCLM.toLinearMap).isPreconnected
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.insert_empty]
      exact one_fibre_exact J m A hJ cJ (hA m) (cA m)

end Liu
