module

public import Liu.AdmissibleContour

@[expose] public section

noncomputable section
open Set MeasureTheory Filter Metric Real Complex
open scoped Topology
namespace Liu

private theorem sideOk_open (s : Bool) : IsOpen {z | sideOk s z} := by
  cases s
  · exact (isOpen_ne_fun continuous_re continuous_const).union (isOpen_lt continuous_im continuous_const)
  · exact (isOpen_ne_fun continuous_re continuous_const).union (isOpen_lt continuous_const continuous_im)

theorem WindowFamily.path_joint_open {U} (W : WindowFamily U) (γ : RealContour) :
    IsOpen {k : ℂ × ℝ | k.1∈U ∧ γ.path k.2∈offCuts (W.L k.1) (W.Q k.1)} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨w,x⟩ ⟨hw,hx⟩
  obtain ⟨hp,hq⟩ := (offCuts_iff_sideOk ..).mp hx
  have Z : ContinuousAt (fun k : ℂ × ℝ => γ.path k.2) (w,x) := (γ.continuous.comp continuous_snd).continuousAt
  have reg {s : Bool} {p : ℂ → ℂ} (d : DifferentiableOn ℂ p U) (h : sideOk s (γ.path x-p w)) :
      ∀ᶠ k : ℂ × ℝ in 𝓝 (w,x), sideOk s (γ.path k.2-p k.1) := by
    have H : ContinuousAt (fun k : ℂ × ℝ => γ.path k.2-p k.1) (w,x) :=
      Z.sub ((d.differentiableAt (W.openSet.mem_nhds hw)).continuousAt.comp continuous_fst.continuousAt)
    exact H.preimage_mem_nhds ((sideOk_open s).mem_nhds h)
  have L := Filter.eventually_all.mpr (fun i => reg (W.dl i) (hp i))
  have Q := Filter.eventually_all.mpr (fun j => reg (W.dq j) (hq j))
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (W.openSet.mem_nhds hw),L,Q] with k hk hl hq using
    ⟨hk,(offCuts_iff_sideOk ..).mpr ⟨hl,hq⟩⟩

theorem WindowFamily.compact_neighborhood {U} (W : WindowFamily U) {w : ℂ} (hw : w∈U) :
    ∃ r>0, closedBall w r⊆U := by
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp (W.openSet.mem_nhds hw)
  exact ⟨r/2,half_pos hr,(closedBall_subset_ball (half_lt_self hr)).trans hs⟩

theorem WindowFamily.pathDomain_open {U} (W : WindowFamily U) (γ : RealContour) : IsOpen (W.pathDomain γ) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨hu,hγ⟩
  obtain ⟨r,hr,hball⟩ := W.compact_neighborhood hu
  obtain ⟨B,hB,hbounds⟩ := W.shape_bound (isCompact_closedBall w r) hball
  obtain ⟨T,hT,ht⟩ := γ.tail
  let R := max T (B+1)
  let E := {k : ℂ × ℝ | k.1∈U ∧ γ.path k.2∈offCuts (W.L k.1) (W.Q k.1)}
  have hE : ({w}:Set ℂ) ×ˢ Icc (-R) R ⊆ E := by
    rintro ⟨s,x⟩ ⟨he,_⟩; have es : s=w := mem_singleton_iff.mp he; subst s; exact ⟨hu,hγ x⟩
  obtain ⟨V,A,hV,_,hv,ha,hVA⟩ := generalized_tube_lemma isCompact_singleton isCompact_Icc (W.path_joint_open γ) hE
  filter_upwards [hV.mem_nhds (hv (mem_singleton _)),closedBall_mem_nhds w hr] with s hs hb
  refine ⟨hball hb,fun x => ?_⟩
  by_cases hx : |x|≤R
  · exact (hVA (show (s,x)∈V ×ˢ A from ⟨hs,ha (abs_le.mp hx)⟩)).2
  · have hx' := lt_of_not_ge hx
    rw [ht x ((le_max_left ..).trans hx'.le)]
    have bound := hbounds s hb
    have ne (p : ℂ) (hn : ‖p‖≤B) : x≠p.re := by
      intro e; have abs := Complex.abs_re_le_norm p
      have H : B+1≤R := le_max_right ..
      rw [←e] at abs; linarith
    exact ⟨fun i e => False.elim (ne _ (bound.2.1 i) e),fun j e => False.elim (ne _ (bound.2.2.1 j) e)⟩

end Liu
