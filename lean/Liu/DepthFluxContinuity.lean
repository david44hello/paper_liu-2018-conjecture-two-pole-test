module

public import Liu.FarDeficit
public import Liu.DepthTraceContinuity

@[expose] public section

noncomputable section
open Set Real Filter MeasureTheory Metric
open scoped Topology
namespace Liu

/-- Domination of the boundary field during downward translation by a single
fixed sum of isolated traces, square integrable on the entire real line. -/
theorem PickSum.depth_field_envelope {n : ℕ} (p : PickSum n) :
    ∃ H : ℝ → ℝ, Integrable (fun x => H x^2) ∧
      ∀ t : ℝ, 0≤t → ∀ x : ℝ, ‖field (depthTranslate p.value t) x‖≤H x := by
  let h := fun (i : Fin n) (x : ℝ) => p.weight i*isolatedTrace (p.location i).re (-(p.location i).im) x
  let H := fun x => ∑ i, h i x
  have hi (i : Fin n) : MemLp (h i) 2 volume :=
    (isolatedTrace_memLp _ (neg_pos.mpr (p.below i))).const_mul _
  have hL : MemLp H 2 volume := memLp_finsetSum Finset.univ (fun i _ => hi i)
  refine ⟨H,(memLp_two_iff_integrable_sq hL.aestronglyMeasurable).mp hL,?_⟩
  intro t ht x
  have integ i := (isolatedDensity_integral (p.pos i) (p.below i) x).1
  have eqn i := (isolatedDensity_integral (p.pos i) (p.below i) x).2
  have hval := (p.deeper t ht).field_on_boundary x
  rw [p.deeper_value ht] at hval
  rw [hval,norm_mul,Complex.norm_I,one_mul]
  change ‖∫ z, traceDensity (depthTranslate p.value t) x z ∂upperArea‖≤_
  have hbound := norm_integral_le_of_norm_le (integrable_finsetSum _ (fun i _ => integ i))
    (f:=fun z => traceDensity (depthTranslate p.value t) x z)
    ((ae_restrict_iff' upper_open.measurableSet).mpr (ae_of_all _ (fun z hz => p.trace_depth_majorant ht hz x)))
  simpa only [integral_finsetSum _ (fun i _ => integ i),eqn,H,h] using hbound

def boundaryFlux (S : ℂ → ℂ) :=
  (∫ x : ℝ, ‖field S x‖^2-k₀*‖S x‖^2)/π

theorem PickSum.depth_flux_continuous {n : ℕ} (p : PickSum n) :
    ContinuousOn (fun t : ℝ => boundaryFlux (depthTranslate p.value t)) (Ici 0) := by
  obtain ⟨H,hH,hv⟩ := p.depth_field_envelope
  have hb := p.bound_pos
  have hk : 0≤k₀ := by unfold k₀; positivity
  let G := fun x : ℝ => ((k₀*p.bound^2)*(1+‖x‖)^(-(2:ℝ)))
  have hG : Integrable G := (integrable_one_add_norm (μ:=(volume:Measure ℝ)) (r:=2) (by norm_num)).const_mul _
  intro t ht
  apply ContinuousWithinAt.div_const
  apply tendsto_integral_filter_of_dominated_convergence (fun x => H x^2+G x) _ _ (hH.add hG) _
  · filter_upwards [self_mem_nhdsWithin (s:=Ici (0:ℝ)) (a:=t)] with u hu
    have hf := (field_measurable (depthTranslate p.value u)).comp Complex.measurable_ofReal
    have hS : Measurable (fun x : ℝ => depthTranslate p.value u x) := by unfold depthTranslate PickSum.value pole; fun_prop
    exact ((hf.norm.pow_const 2).sub ((hS.norm.pow_const 2).const_mul k₀)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin (s:=Ici (0:ℝ)) (a:=t)] with u hu
    apply ae_of_all; intro x
    let z := (x:ℂ)+(u:ℂ)*Complex.I
    have hz : 0≤z.im := by simpa [z] using hu
    have hr : ‖x‖≤‖z‖ := by simpa [z,Real.norm_eq_abs] using Complex.abs_re_le_norm z
    have hS : ‖depthTranslate p.value u x‖≤p.bound/(1+‖x‖) :=
      (p.global_decay hz).trans (div_le_div_of_nonneg_left hb.le (by positivity) (by linarith))
    apply (norm_sub_le ..).trans
    simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖field (depthTranslate p.value u) x‖),abs_of_nonneg (mul_nonneg hk (sq_nonneg ‖depthTranslate p.value u x‖))]
    apply add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hv u hu x) 2)
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hS 2) hk).trans_eq
    change k₀*(p.bound/(1+‖x‖))^2=k₀*p.bound^2*(1+‖x‖)^(-(2:ℝ))
    rw [Real.rpow_neg (by positivity),Real.rpow_two,div_pow,div_eq_mul_inv,mul_assoc]
  · apply ae_of_all; intro x
    have hF := p.depth_trace_continuous x t ht
    have hz : 0≤((x:ℂ)+(t:ℂ)*Complex.I).im := by simpa using ht
    have hmap : ContinuousAt (fun u : ℝ => (x:ℂ)+(u:ℂ)*Complex.I) t := by fun_prop
    have hS : ContinuousAt (fun u : ℝ => depthTranslate p.value u x) t := (p.hasDerivAt hz).continuousAt.comp (f:=fun u : ℝ => (x:ℂ)+(u:ℂ)*Complex.I) hmap
    exact ((hF.norm.pow 2).sub ((hS.continuousWithinAt.norm.pow 2).const_mul k₀)).tendsto

/-- Continuity of the actual right-hand side of the depth-flux identity. -/
theorem flux_continuous_positive (s γ : ℝ) (hγ : γ∈Icc 0 (π/2)) :
    ContinuousOn (flux s γ) (Ioi 0) := by
  intro u hu
  have hu' : 0<u := hu
  let b := u/2
  have hb : 0<b := half_pos hu'
  let p := (normalPair s γ b hγ hb).toPick
  have he (t : ℝ) : depthTranslate p.value (t-b)=normalSum s γ t := by
    rw [show p.value=normalSum s γ b from normalPair_value ..,edge_coordinates s γ b,edge_coordinates s γ t]
    funext z; dsimp only [depthTranslate]; congr 1; push_cast; ring
  have ht : 0<u-b := by dsimp [b]; linarith
  have hh := (p.depth_flux_continuous.continuousAt (Ici_mem_nhds ht)).comp (f:=fun t : ℝ => t-b)
    (show ContinuousAt (fun t : ℝ => t-b) u by fun_prop)
  have hs : (fun t : ℝ => boundaryFlux (depthTranslate p.value (t-b)))=flux s γ := by
    funext t; rw [he]; rfl
  have hc : ContinuousAt (fun t : ℝ => boundaryFlux (depthTranslate p.value (t-b))) u := hh
  rw [hs] at hc; exact hc.continuousWithinAt

end Liu
