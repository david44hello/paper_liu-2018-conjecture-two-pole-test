module

public import Liu.DiscMoments

@[expose] public section

noncomputable section
open Set MeasureTheory Real Metric
open scoped ComplexConjugate
namespace Liu

/-- Evaluation for any holomorphic function integrable against this one kernel. -/
theorem bergman_reproducing_integrable {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f upper)
    {z : ℂ} (hz : z ∈ upper) (hi : Integrable (fun w => f w*conj (bergmanKernel z w)) upperArea) :
    (∫ w, f w*conj (bergmanKernel z w) ∂upperArea) = f z := by
  let c := conj (-(z-conj z)⁻¹)
  have hn : z-conj z ≠ 0 := by
    intro he; have hh := congrArg Complex.im (sub_eq_zero.mp he)
    simp at hh; change 0<z.im at hz; linarith
  have hc : c≠0 := by exact (map_ne_zero (starRingEnd ℂ)).mpr (neg_ne_zero.mpr (inv_ne_zero hn))
  have heq (w : ℂ) (hw : w∈disc) : ‖cayleyJac z w‖^2 • (f (cayley z w)*conj (bergmanKernel z (cayley z w))) =
      cayleyPull z f w*c := by
    dsimp only [c]
    rw [←cayleyPull_kernel hz hw]
    simp only [cayleyPull,Complex.real_smul,Complex.ofReal_pow,←Complex.mul_conj',map_mul]
    ring
  have hpull := (cayley_integrable_iff hz _).mp hi
  have hid : IntegrableOn (fun w => cayleyPull z f w*c) disc area :=
    hpull.congr_fun heq Metric.isOpen_ball.measurableSet
  have hf : IntegrableOn (cayleyPull z f) disc area := by
    change Integrable (fun w => cayleyPull z f w) (area.restrict disc)
    simpa only [mul_assoc,mul_inv_cancel₀ hc,mul_one] using hid.mul_const c⁻¹
  rw [upperArea,cayley_area_integral hz,setIntegral_congr_fun (s:=disc) Metric.isOpen_ball.measurableSet heq,
    integral_mul_const,disc_mean_integrable hf (cayleyPull_holomorphic hz hd)]
  dsimp only [c]
  simp only [cayleyPull,cayley,cayleyJac,mul_zero,sub_zero,div_one,one_pow,map_neg,map_inv₀,map_sub,Complex.conj_conj]
  rw [show conj z-z = -(z-conj z) by ring,inv_neg,neg_neg]
  field_simp [hn]

def uniquenessProbe (m : ℕ) (w : ℂ) := (w-Complex.I)^m/(w+Complex.I)^(m+3)

private theorem unit_disc_coordinate {w : ℂ} (hw : w ∈ upper) : ‖cayleyInv Complex.I w‖ < 1 := by
  have hi : Complex.I ∈ upper := by change 0<Complex.I.im; norm_num
  simpa [disc] using (cayley_inv_right hi hw).1

private theorem resolvent_kernel_ratio {a w : ℂ} (ha : a∈upper) (hw : w∈upper) :
    bergmanKernel a w = bergmanKernel Complex.I w *
      ((1-conj (cayleyInv Complex.I a))/(1-conj (cayleyInv Complex.I a)*cayleyInv Complex.I w))^2 := by
  have wn : w+Complex.I≠0 := fun h => by
    have hh := congrArg Complex.im h; simp at hh; change 0<w.im at hw; linarith
  have an' : a+Complex.I≠0 := fun h => by
    have hh := congrArg Complex.im h; simp at hh; change 0<a.im at ha; linarith
  have an : conj a-Complex.I≠0 := by
    have := (map_ne_zero (starRingEnd ℂ)).mpr an'
    simpa [sub_eq_add_neg] using this
  have wa : w-conj a≠0 := fun h => by
    have hh := congrArg Complex.im (sub_eq_zero.mp h); simp at hh
    change 0<w.im at hw; change 0<a.im at ha; linarith
  have hsmall := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (unit_disc_coordinate ha)
    (unit_disc_coordinate hw).le
  have hq : 1-conj (cayleyInv Complex.I a)*cayleyInv Complex.I w≠0 := fun h => by
    have hh := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one,norm_mul,Complex.norm_conj] at hh
    linarith
  have hc : conj (cayleyInv Complex.I a)=(conj a+Complex.I)/(conj a-Complex.I) := by
    simp [cayleyInv,sub_eq_add_neg]
  have hr : (1-conj (cayleyInv Complex.I a))/(1-conj (cayleyInv Complex.I a)*cayleyInv Complex.I w) =
      (w+Complex.I)/(w-conj a) := by
    apply (div_eq_div_iff hq wa).mpr
    rw [hc,cayleyInv,Complex.conj_I,sub_neg_eq_add]
    field_simp [wn,an] <;> ring
  rw [hr,bergmanKernel,bergmanKernel,Complex.conj_I,sub_neg_eq_add]
  field_simp [wn,wa]

/-- Vanishing of all the weighted probes in Appendix A.1 forces a holomorphic
function to vanish whenever its central Bergman pairing is absolutely integrable. -/
theorem uniqueness_of_probe_moments {V : ℂ → ℂ} (hd : DifferentiableOn ℂ V upper)
    (hint : Integrable (fun w => V w*conj (bergmanKernel Complex.I w)) upperArea)
    (hprobe : ∀ m : ℕ, ∫ w, V w*conj (uniquenessProbe m w) ∂upperArea = 0) :
    ∀ a ∈ upper, V a=0 := by
  let q := fun w => conj (cayleyInv Complex.I w)
  let g := fun w => V w*conj (bergmanKernel Complex.I w)
  have hq : Measurable q := by dsimp [q,cayleyInv]; fun_prop
  have hb : ∀ᵐ w ∂upperArea, ‖q w‖<1 := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
    simpa [q] using unit_disc_coordinate hw
  let J := fun m : ℕ => ∫ w, g w*q w^m ∂upperArea
  have hs (m : ℕ) : J m=J (m+1) := by
    apply sub_eq_zero.mp
    rw [show J m-J (m+1) = ∫ w, g w*q w^m-g w*q w^(m+1) ∂upperArea from
      (integral_sub (moments_integrable hint hq hb m) (moments_integrable hint hq hb (m+1))).symm]
    have he : ∀ᵐ w ∂upperArea, g w*q w^m-g w*q w^(m+1)= (2*Complex.I)*(V w*conj (uniquenessProbe m w)) := by
      filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
      have hn : w+Complex.I≠0 := fun h => by
        have hh := congrArg Complex.im h; simp at hh; change 0<w.im at hw; linarith
      let Q := cayleyInv Complex.I w
      have hi : bergmanKernel Complex.I w*Q^m*(1-Q) = (-2*Complex.I)*uniquenessProbe m w := by
        dsimp only [Q,cayleyInv,bergmanKernel,uniquenessProbe]
        rw [Complex.conj_I,sub_neg_eq_add,div_pow,pow_add]
        field_simp [hn] <;> ring
      calc
        _ = V w*conj (bergmanKernel Complex.I w*Q^m*(1-Q)) := by
          dsimp only [q,g,Q]; simp only [map_mul,map_pow,map_sub,map_one,pow_succ]; ring
        _ = _ := by rw [hi]; simp only [map_mul,map_neg,map_ofNat,Complex.conj_I]; ring
    rw [integral_congr_ae he,integral_const_mul,hprobe,mul_zero]
  have hz : J 0=0 := by
    have hc (m : ℕ) : J m=J 0 := by induction m with | zero => rfl | succ n ih => exact (hs n).symm.trans ih
    exact tendsto_nhds_unique tendsto_const_nhds ((moments_vanish_at_infinity hint hq hb).congr hc)
  have hJ (m : ℕ) : J m=0 := by induction m with | zero => exact hz | succ n ih => exact (hs n).symm.trans ih
  intro a ha
  let c := cayleyInv Complex.I a
  obtain ⟨h1,hM1⟩ := vanishing_moments_div hint hq hb hJ (unit_disc_coordinate ha)
  obtain ⟨h2,hM2⟩ := vanishing_moments_div h1 hq hb hM1 (unit_disc_coordinate ha)
  let G := fun w => (g w/(1-c*q w))/(1-c*q w)
  have hGI : Integrable G upperArea := h2
  have hG0 : ∫ w, G w ∂upperArea = 0 := by simpa only [pow_zero,mul_one] using hM2 0
  have he : (fun w => V w*conj (bergmanKernel a w)) =ᵐ[upperArea] (fun w => (1-c)^2*G w) := by
    filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with w hw
    rw [resolvent_kernel_ratio ha hw]
    dsimp only [c,G,g,q]
    simp only [map_mul,map_pow,map_div₀,map_sub,map_one,map_inv₀,Complex.conj_conj,div_pow,div_eq_mul_inv,inv_pow]; ring
  rw [←bergman_reproducing_integrable hd ha ((hGI.const_mul _).congr he.symm),integral_congr_ae he,integral_const_mul,hG0,mul_zero]

end Liu
