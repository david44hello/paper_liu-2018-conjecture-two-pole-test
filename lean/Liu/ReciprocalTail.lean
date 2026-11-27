module

public import Liu.Anchor

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Liu

/-- The reciprocal-depth extension on the closed physical top interval. -/
def topExtension (s γ T : ℝ) : Prop :=
  ∃ g : ℝ → ℝ, ContinuousOn g (Icc 0 (1/T)) ∧
    ∀ t : ℝ, T ≤ t → t^2*flux s γ t = g (1/t)

theorem top_flux_bounded {s γ T : ℝ} (hT : 0<T) (he : topExtension s γ T) :
    ∃ M : ℝ, 0≤M ∧ ∀ t : ℝ, T ≤ t → |flux s γ t| ≤ M/t^2 := by
  obtain ⟨g,hg,heq⟩ := he
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image (hg.abs)
  refine ⟨max 0 C,le_max_left ..,?_⟩
  intro t ht
  have hp := hT.trans_le ht
  have hm : 1/t ∈ Icc 0 (1/T) := ⟨(one_div_pos.mpr hp).le,one_div_le_one_div_of_le hT ht⟩
  have hc : |g (1/t)| ≤ C := hC ⟨1/t,hm,rfl⟩
  rw [←heq t ht,abs_mul,abs_of_nonneg (sq_nonneg _)] at hc
  exact (le_div_iff₀ (sq_pos_of_pos hp)).mpr (by linarith [le_max_right 0 C])

theorem integrable_flux_tail {s γ T u : ℝ} (hT : 0<T) (hu : 0<u)
    (hg : γ ∈ Icc 0 (Real.pi/2)) (hf : Certificate.fluxIdentity)
    (hc : ContinuousOn (flux s γ) (Ioi 0)) (he : topExtension s γ T) :
    IntegrableOn (flux s γ) (Ioi u) := by
  let v := max u T
  have hv : 0<v := hu.trans_le (le_max_left ..)
  obtain ⟨M,hM,hbound⟩ := top_flux_bounded hT he
  have hrs := integrableOn_Ioi_rpow_of_lt (c := v) (a := (-2:ℝ)) (by norm_num) hv
  have hmajor := hrs.const_mul M
  have hhi : IntegrableOn (flux s γ) (Ioi v) := by
    apply hmajor.mono' ((hc.mono (Ioi_subset_Ioi hv.le)).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := v))] with t ht
    have hr : 0 < t := hv.trans ht
    simpa [Real.norm_eq_abs,Real.rpow_neg hr.le,div_eq_mul_inv] using
      hbound t (le_trans (le_max_right u T) ht.le)
  have hlo : IntegrableOn (flux s γ) (Ioc u v) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_max_left ..)).mp ((hf s γ hg u v hu (le_max_left ..)).1)
  apply (hlo.union hhi).mono_set
  intro x hx
  by_cases h : x ≤ v
  · exact Or.inl ⟨hx,h⟩
  · exact Or.inr (lt_of_not_ge h)

end Liu
