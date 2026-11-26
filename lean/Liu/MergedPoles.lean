import Liu.ClusterDensity
import Liu.Anchor
import Liu.EdgeTrace

noncomputable section
open Set Real Filter MeasureTheory Metric
open scoped Topology
namespace Liu

private theorem witnessDensity_local {n : ℕ} (p : PickSum n) {W : ℂ → ℂ}
    (hw : isWitness W) (R : ℝ) : IntegrableOn (witnessDensity p.value W) (halfDisc R) area := by
  let U := {w : ℂ | 0≤w.im}
  let K := U ∩ closedBall 0 R
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) R).inter_left (isClosed_le continuous_const Complex.continuous_im)
  have hS : ContinuousOn p.value U := fun w hw => (p.hasDerivAt hw).continuousAt.continuousWithinAt
  have ha : ContinuousOn (fun w => (p.value w).arg) U := fun w h =>
    (Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr (Or.inr (p.value_im_pos h).ne'))).comp_continuousWithinAt (hS w h)
  have hD : ContinuousOn (witnessDensity p.value W) U :=
    (hS.norm.pow 2).mul (continuousOn_const.sub (((Complex.continuous_ofReal.comp_continuousOn ha).sub hw.2.1).norm.pow 2))
  exact ((hD.mono (show K⊆U from inter_subset_left)).integrableOn_compact hK).mono_set
    fun z hz => ⟨(show 0<z.im from hz.1).le,ball_subset_closedBall hz.2⟩

private theorem truncatedWitness_eq_int (S W : ℂ → ℂ) (R : ℝ) :
    truncatedWitness S W R=∫ z in halfDisc R, witnessDensity S W z ∂area := by
  apply setIntegral_congr_fun (upper_open.measurableSet.inter isOpen_ball.measurableSet)
  intro z _; dsimp only [witnessDensity]; ring

/-- Compare two witness finite parts by an integrable majorant for the change
in density, using the optimal witness of the reference sum. -/
theorem deficit_lower_of_witness_majorant {n m : ℕ} (p : PickSum n) (q : PickSum m)
    {g : ℂ → ℝ} (hg : Integrable g upperArea) (hg0 : ∀ z∈upper, 0≤g z)
    (hpq : ∀ z∈upper, witnessDensity q.value (optimalWitness q.value) z -
      witnessDensity p.value (optimalWitness q.value) z ≤ g z) :
    deficit q.value-(∫ z, g z ∂upperArea)≤deficit p.value := by
  let W := optimalWitness q.value
  have hw := q.optimalWitness_isWitness
  obtain ⟨_,hP,hPl,hPle,_⟩ := p.witness_identity.2 W hw
  obtain ⟨_,hQ,hQl,_,hQeq⟩ := q.witness_identity.2 W hw
  have he := hQeq.mpr (fun _ _ => rfl)
  rw [←hQl,he] at hQ
  rw [←hPl] at hP
  apply le_trans _ hPle
  apply le_of_tendsto_of_tendsto' (hQ.sub_const (∫ z, g z ∂upperArea)) hP
  intro R
  have hg' : IntegrableOn g upper area := hg
  have hsub : halfDisc R⊆upper := inter_subset_left
  have h := setIntegral_mono_on ((witnessDensity_local q hw R).sub (witnessDensity_local p hw R)) (hg'.mono_set hsub)
    (upper_open.measurableSet.inter isOpen_ball.measurableSet) (fun z hz => hpq z hz.1)
  have hr : (∫ z in halfDisc R, g z ∂area)≤∫ z, g z ∂upperArea :=
    setIntegral_mono_set hg' ((ae_restrict_iff' upper_open.measurableSet).mpr (ae_of_all _ hg0)) (ae_of_all _ fun _ hz => hsub hz)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (witnessDensity_local q hw R) (witnessDensity_local p hw R),
    ←truncatedWitness_eq_int,←truncatedWitness_eq_int] at h
  linarith

/-- A quantitative finite-part lower bound at the true mass centre. -/
theorem Pair.mergedPole_lower (p : Pair) (hd : p.separation≤ -p.massCentre.im/4) :
    singleConstant*p.mass^2-15*p.a₁*p.a₂*p.separation^2/(-p.massCentre.im)^2≤deficit p.value := by
  let g := fun z : ℂ => (60*p.a₁*p.a₂*p.separation^2)*(‖z-p.massCentre‖^4)⁻¹
  have hK := fourth_pole_integral p.massCentre_below
  have hg : Integrable g upperArea := hK.1.const_mul _
  have hg0 (z : ℂ) (_ : z∈upper) : 0≤g z := by
    have := p.ha₁; have := p.ha₂; dsimp only [g]; positivity
  have he : p.toPick.value=p.value := by funext z; simp [Pair.toPick,PickSum.value,Pair.value,Fin.sum_univ_two]
  have H := deficit_lower_of_witness_majorant p.toPick p.centrePick hg hg0 (by
    intro z hz; rw [he]; exact (abs_sub_le_iff.mp (p.cluster_density_bound hd (le_of_lt hz))).2)
  rw [he,p.centrePick_value,singlePole_deficit p.mass p.massCentre p.mass_pos p.massCentre_below,
    show (∫ z, g z ∂upperArea) = 15*p.a₁*p.a₂*p.separation^2/(-p.massCentre.im)^2 by
      dsimp [g]; rw [integral_const_mul,hK.2]; ring] at H
  exact H

/-- Lemma 4.4, with the constant and denominator of the printed statement. -/
theorem Pair.mergedPole_deficit (p : Pair) (hd : p.separation≤ -p.massCentre.im/4) :
    let u := -p.massCentre.im
    singleConstant*p.mass^2-16.2*p.a₁*p.a₂*p.separation^2/(u*(u-p.separation))≤deficit p.value := by
  let u := -p.massCentre.im
  have hu : 0<u := neg_pos.mpr p.massCentre_below
  have hsub : 0<u-p.separation := by change p.separation≤u/4 at hd; linarith
  have hd0 : 0≤p.separation := norm_nonneg _
  have hA : 0≤p.a₁*p.a₂*p.separation^2 := by have := p.ha₁; have := p.ha₂; positivity
  apply le_trans _ (p.mergedPole_lower hd)
  apply sub_le_sub_left
  change 15*p.a₁*p.a₂*p.separation^2/u^2≤16.2*p.a₁*p.a₂*p.separation^2/(u*(u-p.separation))
  apply div_le_div₀ (by linarith only [show 0≤15*(p.a₁*p.a₂*p.separation^2) from mul_nonneg (by norm_num) hA]) _ (mul_pos hu hsub) _
  · nlinarith only [hA]
  · nlinarith only [mul_nonneg hu.le hd0]

theorem normalized_deep_cluster : deepCluster := by
  intro s γ T hγ hT
  have ht : 0<T := by linarith
  let p := normalPair s γ T hγ ht
  have hm : p.mass=1 := by simp [p,normalPair,Pair.mass]
  have hμ : p.massFraction=normalMass s := by rw [Pair.massFraction,hm,div_one]; rfl
  have hdir := direction_norm γ
  have hs : p.separation=1 := by
    change ‖-(T:ℂ)*Complex.I-(-(T:ℂ)*Complex.I+direction γ)‖=1
    rw [show -(T:ℂ)*Complex.I-(-(T:ℂ)*Complex.I+direction γ)= -direction γ by ring,norm_neg,hdir]
  have hcent : -p.massCentre.im=T+(1-normalMass s)*sin γ := by
    rw [Pair.massCentre]; simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.sub_im,zero_mul,add_zero,hμ]; simp [p,normalPair,direction_im]; ring
  have hγ' := sin_nonneg_of_nonneg_of_le_pi hγ.1 (hγ.2.trans (by linarith [pi_pos]))
  have h₂ : 0<1-normalMass s := p.ha₂
  have hdep : T≤ -p.massCentre.im := by rw [hcent]; linarith [mul_nonneg h₂.le hγ']
  have hg := p.mergedPole_lower (by rw [hs]; linarith)
  have hval : p.value=normalSum s γ T := rfl
  rw [hm,hs,hval] at hg
  have hquad : p.a₁*p.a₂≤1/4 := by
    change normalMass s*(1-normalMass s)≤1/4
    nlinarith [sq_nonneg (normalMass s-1/2)]
  have hden : 0<T*(T-1) := mul_pos ht (by linarith)
  have hden' : T*(T-1)≤(-p.massCentre.im)^2 := by nlinarith [pow_le_pow_left₀ ht.le hdep 2]
  have hcmp : 15*p.a₁*p.a₂/(-p.massCentre.im)^2≤4.05/(T*(T-1)) := by
    apply div_le_div₀ (by have := p.ha₁; have := p.ha₂; positivity) _ hden hden'
    nlinarith only [hquad]
  simp only [one_pow,mul_one] at hg
  unfold margin; linarith

theorem anchor_of_flux_identity (hf : Certificate.fluxIdentity)
    {s γ u L : ℝ} (hg : γ∈Icc 0 (π/2)) (hu : 0<u)
    (conv : Tendsto (fun T => ∫ t in u..T, flux s γ t) atTop (𝓝 L)) :
    (singleConstant-k₀)-L≤ margin s γ u :=
  anchor_of_cluster_and_flux normalized_deep_cluster hf hg hu conv

end Liu
