import Liu.BandAverage
import Liu.SmallMassDeficit

noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
namespace Liu

theorem depthTranslate_add (S : ℂ → ℂ) (s t : ℝ) :
    depthTranslate (depthTranslate S s) t=depthTranslate S (s+t) := by
  funext z; dsimp [depthTranslate]; congr 1; push_cast; ring

/-- Translating an arbitrary finite Pick sum downwards differentiates its
actual finite part to the physical boundary flux. -/
theorem PickSum.depth_deficit_hasDerivAt {n : ℕ} (p : PickSum n) {a : ℝ} (ha : 0<a) :
    HasDerivAt (fun t : ℝ => deficit (depthTranslate p.value t))
      (boundaryFlux (depthTranslate p.value a)) a := by
  let l := 𝓝[≠] a
  let u := fun t : ℝ => min t a
  let v := fun t : ℝ => max t a
  let h := fun t : ℝ => |t-a|
  let f := fun t : ℝ => deficit (depthTranslate p.value t)
  let G := fun t => witnessDifference (depthTranslate p.value (v t))
    (depthTranslate (optimalWitness (depthTranslate p.value (u t))) (h t))
  have hid : Tendsto id l (𝓝 a) := nhdsWithin_le_nhds
  have hu : Tendsto u l (𝓝 a) := by simpa only [u,id_eq,min_self] using hid.min (tendsto_const_nhds (x:=a))
  have hh : Tendsto h l (𝓝 0) := by simpa only [h,id_eq,sub_self,abs_zero] using (hid.sub_const a).abs
  have hr : ∀ᶠ t in l, 0≤u t ∧ 0<h t := by
    filter_upwards [hid.eventually_const_lt ha,self_mem_nhdsWithin (a:=a) (s:={a}ᶜ)] with t ht hne
    exact ⟨le_min ht.le ha.le,abs_pos.mpr (sub_ne_zero.mpr (show t≠a from hne))⟩
  have huv (t : ℝ) : u t+h t=v t := by
    rcases le_total t a with H | H
    · simp [u,v,h,H,abs_of_nonpos (sub_nonpos.mpr H)]
    · simp [u,v,h,H,abs_of_nonneg (sub_nonneg.mpr H)]
  have hstrip := p.band_average_limit ha.le hu hh hr
  obtain ⟨K,hK,henergy⟩ := p.depth_increment_energy
  have hE : Tendsto (fun t => energy (G t)/h t) l (𝓝 0) := by
    refine squeeze_zero' (g:=fun t => K*(h t)^(1/2:ℝ)) (Eventually.of_forall fun t => div_nonneg (sq_nonneg _) (abs_nonneg _)) ?_ ?_
    · filter_upwards [hr] with t ⟨htu,hth⟩
      have H := (henergy (u t) htu (h t) hth.le).2.2
      rw [PickSum.deeper_value,PickSum.deeper_value,depthTranslate_add,huv] at H
      apply (div_le_iff₀ hth).mpr
      have he : K*(h t)^(3/2:ℝ)=(K*(h t)^(1/2:ℝ))*(h t) := by
        rw [mul_assoc,←rpow_add_one hth.ne']; norm_num
      exact H.trans_eq he
    · simpa using (hh.rpow_const_nhds_zero (by norm_num : (0:ℝ)<1/2)).const_mul K
  have hslope : ∀ᶠ t in l, slope f a t =
    -(∫ z in depthBand (h t),physicalDensity (depthTranslate p.value (u t)) z ∂area)/(h t)+energy (G t)/(h t) := by
    filter_upwards [hr] with t ⟨htu,hth⟩
    have H := (p.deeper (u t) htu).depth_deficit_difference hth.le
    dsimp only at H
    rw [PickSum.deeper_value,PickSum.deeper_value,depthTranslate_add,huv] at H
    change f (v t)-f (u t) = _ + energy (G t) at H
    rw [←add_div,←H,slope_def_field]
    rcases le_total t a with ht | ht
    · simp only [u,v,h,min_eq_left ht,max_eq_right ht,abs_of_nonpos (sub_nonpos.mpr ht),div_neg,neg_div,neg_neg]; rw [←neg_div,neg_sub]
    · simp only [u,v,h,min_eq_right ht,max_eq_left ht,abs_of_nonneg (sub_nonneg.mpr ht)]
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply Filter.Tendsto.congr' (hslope.mono fun t h => h.symm)
  simpa only [neg_div,neg_neg,add_zero] using hstrip.neg.add hE

private theorem PickSum.earlier_depth {n : ℕ} (p : PickSum n) {a : ℝ} (ha : ∀ i, (p.location i).im<a) :
    ∃ b<a, ∃ q : PickSum n, q.value=depthTranslate p.value b := by
  letI : Nonempty (Fin n) := ⟨⟨0,p.nonempty⟩⟩
  obtain ⟨i,hi⟩ := Finite.exists_max (fun i => (p.location i).im)
  obtain ⟨b,hb,hab⟩ := exists_between (ha i)
  let q : PickSum n :=
    { nonempty := p.nonempty
      weight := p.weight
      location := fun j => p.location j-(b:ℂ)*Complex.I
      pos := p.pos
      below := fun j => by simp; linarith [hi j] }
  have he : q.value=depthTranslate p.value b := by
    funext z; dsimp only [q,PickSum.value,depthTranslate,pole]
    apply Finset.sum_congr rfl; intro j _
    rw [show z-(p.location j-(b:ℂ)*Complex.I)=z+(b:ℂ)*Complex.I-p.location j by ring]
  exact ⟨b,hab,q,he⟩

/-- The same derivative holds at any translated depth for which every pole
is strictly below the observation line. -/
theorem PickSum.flux_law_at {n : ℕ} (p : PickSum n) {a : ℝ} (ha : ∀ i, (p.location i).im<a) :
    HasDerivAt (fun t : ℝ => deficit (depthTranslate p.value t))
      (boundaryFlux (depthTranslate p.value a)) a := by
  obtain ⟨b,hab,q,he⟩ := p.earlier_depth ha
  have H := (q.depth_deficit_hasDerivAt (sub_pos.mpr hab)).comp a ((hasDerivAt_id a).sub_const b)
  have hfun : (fun t : ℝ => deficit (depthTranslate q.value t)) ∘ (fun t : ℝ => t-b)=
      (fun t => deficit (depthTranslate p.value t)) := by
    funext t; rw [Function.comp_apply,he,depthTranslate_add]; simp
  change HasDerivAt ((fun t => deficit (depthTranslate q.value t)) ∘ (fun t : ℝ => t-b)) (boundaryFlux (depthTranslate q.value (a-b))*1) a at H
  rwa [hfun,he,depthTranslate_add,show b+(a-b)=a by ring,mul_one] at H

theorem PickSum.flux_continuousAt_valid_depth {n : ℕ} (p : PickSum n) {a : ℝ}
    (ha : ∀ i, (p.location i).im<a) :
    ContinuousAt (fun t => boundaryFlux (depthTranslate p.value t)) a := by
  obtain ⟨b,hab,q,he⟩ := p.earlier_depth ha
  have H := (q.depth_flux_continuous.continuousAt (Ici_mem_nhds (sub_pos.mpr hab))).comp (f:=fun t : ℝ => t-b)
    (show ContinuousAt (fun t : ℝ => t-b) a by fun_prop)
  have hfun : (fun t : ℝ => boundaryFlux (depthTranslate q.value t)) ∘ (fun t : ℝ => t-b)=
      (fun t => boundaryFlux (depthTranslate p.value t)) := by
    funext t; rw [Function.comp_apply,he,depthTranslate_add]; simp
  rwa [hfun] at H

theorem PickSum.finite_depth_flux_law {n : ℕ} (p : PickSum n) {u v : ℝ} (hu : ∀ i, (p.location i).im<u)
    (huv : u≤v) :
    let F := fun t => boundaryFlux (depthTranslate p.value t)
    IntervalIntegrable F volume u v ∧
    deficit (depthTranslate p.value u) = deficit (depthTranslate p.value v) - ∫ t in u..v,F t := by
  have hv {t : ℝ} (ht : t∈uIcc u v) : ∀ i,(p.location i).im<t := by
    rw [uIcc_of_le huv] at ht; exact fun i => (hu i).trans_le ht.1
  have hc : ContinuousOn (fun t => boundaryFlux (depthTranslate p.value t)) (uIcc u v) :=
    fun t ht => (p.flux_continuousAt_valid_depth (hv ht)).continuousWithinAt
  have hi := hc.intervalIntegrable (μ:=volume)
  refine ⟨hi,?_⟩
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => p.flux_law_at (hv ht)) hi
  linarith

theorem depth_flux_hasDerivAt (s γ : ℝ) (hγ : γ∈Icc 0 (π/2)) {u : ℝ} (hu : 0<u) :
    HasDerivAt (margin s γ) (flux s γ u) u := by
  let b := u/2
  have hb : 0<b := half_pos hu
  let p := (normalPair s γ b hγ hb).toPick
  have he (t : ℝ) : depthTranslate p.value (t-b)=normalSum s γ t := by
    rw [show p.value=normalSum s γ b from normalPair_value ..,edge_coordinates s γ b,edge_coordinates s γ t]
    funext z; dsimp only [depthTranslate]; congr 1; push_cast; ring
  have hh := (p.depth_deficit_hasDerivAt (a:=u-b) (by dsimp [b]; linarith)).comp u ((hasDerivAt_id u).sub_const b)
  have hfun : (fun t : ℝ => deficit (depthTranslate p.value t)) ∘ (fun t : ℝ => t-b) =
      fun t => deficit (normalSum s γ t) := by funext t; simp [Function.comp_def,he]
  change HasDerivAt ((fun t => deficit (depthTranslate p.value t)) ∘ (fun t : ℝ => t-b)) (boundaryFlux (depthTranslate p.value (u-b))*1) u at hh
  rw [hfun,he,mul_one] at hh
  exact hh.sub_const k₀

theorem depth_flux_contDiff (s γ : ℝ) (hγ : γ∈Icc 0 (π/2)) :
    ContDiffOn ℝ 1 (margin s γ) (Ioi 0) := by
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn]
  refine ⟨fun u hu => (depth_flux_hasDerivAt s γ hγ hu).differentiableAt.differentiableWithinAt,?_⟩
  apply (flux_continuous_positive s γ hγ).congr
  intro u hu; exact (depth_flux_hasDerivAt s γ hγ hu).hasDerivWithinAt.derivWithin (isOpen_Ioi.uniqueDiffOn u hu)

theorem depth_flux_identity : Certificate.fluxIdentity := by
  intro s γ hγ u v hu huv
  have hc := (flux_continuous_positive s γ hγ).mono (show uIcc u v⊆Ioi 0 by
    rw [uIcc_of_le huv]; exact fun t ht => hu.trans_le ht.1)
  have hi := hc.intervalIntegrable (μ:=volume)
  refine ⟨hi,?_⟩
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => depth_flux_hasDerivAt s γ hγ
    (hu.trans_le (uIcc_of_le huv ▸ ht).1)) hi
  linarith

theorem depth_anchor {s γ u L : ℝ} (hγ : γ∈Icc 0 (π/2)) (hu : 0<u)
    (conv : Tendsto (fun T => ∫ t in u..T,flux s γ t) atTop (𝓝 L)) :
    (singleConstant-k₀)-L ≤ margin s γ u := anchor_of_flux_identity depth_flux_identity hγ hu conv

theorem pair_deficit_of_three_inputs (p : Pair) (box : Certificate.boxBounds)
    (small : Certificate.smallDepthEstimate) (mixed : Certificate.mixedEdgeEstimate) :
    k₀*p.mass^2<deficit p.value := pair_deficit_of_four_inputs p box depth_flux_identity small mixed

theorem two_pole_test_of_three_inputs (p : Pair) (box : Certificate.boxBounds)
    (small : Certificate.smallDepthEstimate) (mixed : Certificate.mixedEdgeEstimate) :
    Tendsto (truncatedDeficit p.value) atTop (𝓝 (deficit p.value)) ∧
    k₀*p.mass^2<deficit p.value ∧ p.slope<0 ∧
    ∃ ε₀>0, ∀ ε : ℝ, 0<ε → ε<ε₀ → p.quotientDomain ε ∧ quotient (critical p ε)<k₀ :=
  two_pole_test_of_four_inputs p box depth_flux_identity small mixed

end Liu
