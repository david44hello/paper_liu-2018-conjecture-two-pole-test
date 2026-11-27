module

public import Liu.DiscLogEnergy

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter Finset
open scoped Topology ComplexConjugate
namespace Liu

private def shiftCoeffs (m : ℕ) (a : ℕ → ℂ) (k : ℕ) : ℂ := if m≤k then a (k-m) else 0

private theorem shift_series {a : ℕ → ℂ} {f z : ℂ} (ha : HasSum (fun n => a n*z^n) f) (m : ℕ) :
    HasSum (fun k => shiftCoeffs m a k*z^k) (z^m*f) := by
  apply (hasSum_nat_add_iff' m).mp
  have h0 : (∑ k ∈ range m, shiftCoeffs m a k*z^k)=0 := by
    apply sum_eq_zero; intro k hk; simp [shiftCoeffs,not_le.mpr (mem_range.mp hk)]
  rw [h0,sub_zero]
  apply (ha.mul_left (z^m)).congr_fun
  intro k
  simp [shiftCoeffs,pow_add]; ring

private theorem shift_weight {a : ℕ → ℂ} (ha : Summable (fun k => ‖a k‖^2/((k:ℝ)+1))) (m : ℕ) :
    Summable (fun k => ‖shiftCoeffs m a k‖^2/((k:ℝ)+1)) := by
  apply (summable_nat_add_iff m).mp
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ ha
  intro k; simp only [shiftCoeffs,Nat.le_add_left,if_pos,Nat.add_sub_cancel,Nat.cast_add]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by have := Nat.cast_nonneg (α:=ℝ) m; linarith)

private theorem coeff_shift_ratio {a : ℝ} (ha : 0<a) (m j : ℕ) :
    capCoeff a (j+m)/((j:ℝ)+m+1) = capCoeff a m/((m:ℝ)+1)*(poch (a+m) j/poch ((m:ℝ)+2) j) := by
  induction j with
  | zero => simp [poch]
  | succ j ih =>
    rw [Nat.succ_add,capCoeff_succ]
    have hpoch (u : ℝ) : poch u (j+1)=poch u j*(u+j) := by simp [poch,ascPochhammer_succ_right]
    rw [hpoch,hpoch,Nat.cast_succ,Nat.cast_add]
    have H : capCoeff a (j+m)/((j:ℝ)+m+1)=_ := ih
    have hp := (poch_pos (by positivity : 0<(m:ℝ)+2) j).ne'
    have hj : (j:ℝ)+m+1≠0 := by positivity
    have h1 : (m:ℝ)+2+j≠0 := by positivity
    rw [show (j:ℝ)+1+m+1=m+2+j by ring]
    field_simp [hj,hp,h1] at H ⊢
    linear_combination (norm := ring) (a+m+j)*H

def momentGamma (a b : ℝ) (m : ℕ) := capCoeff a m/((m:ℝ)+1)*
  (Gamma ((m:ℝ)+2)*Gamma (2-a-b)/(Gamma (2-a)*Gamma ((m:ℝ)+2-b)))

theorem discPower_shifted_pairing {a b : ℝ} (ha : a∈Set.Ioo 0 1) (hb : b∈Set.Ioo 0 1) (m : ℕ) :
    (∫ z in disc, conj (z^m)*discPower a z*conj (discPower b z) ∂area) = (momentGamma a b m:ℂ) := by
  let c := fun k : ℕ => (capCoeff b k:ℂ)
  have H := disc_series_pairing (shift_weight (capCoeff_square_summable hb.1 hb.2) m)
    (capCoeff_square_summable ha.1 ha.2) (fun z hz => shift_series (discPower_series b hz) m) (fun z hz => discPower_series a hz)
  let f := fun k : ℕ => conj (shiftCoeffs m c k)*(capCoeff a k:ℂ)/((k:ℂ)+1)
  have hzero : ∑ k ∈ range m, f k=0 := by
    apply sum_eq_zero; intro k hk; simp [f,shiftCoeffs,not_le.mpr (mem_range.mp hk)]
  have L := gauss_sum_positive (a:=a+m) (b:=b) (c:=(m:ℝ)+2) (by have := ha.1; positivity) hb.1 (by linarith [ha.2,hb.2])
  have Hreal : HasSum (fun j => capCoeff b j*(capCoeff a (j+m)/((j:ℝ)+m+1))) (momentGamma a b m) := by
    rw [show (m:ℝ)+2-(a+m)-b=2-a-b by ring,show (m:ℝ)+2-(a+m)=2-a by ring] at L
    apply (L.mul_left (capCoeff a m/((m:ℝ)+1))).congr_fun
    intro j
    rw [coeff_shift_ratio ha.1]
    unfold capCoeff; ring
  have hg := Complex.hasSum_ofReal.mpr Hreal
  have hs : HasSum f (momentGamma a b m:ℂ) := by
    apply (hasSum_nat_add_iff' m).mp; rw [hzero,sub_zero]
    apply hg.congr_fun; intro j
    simp [f,c,shiftCoeffs,Complex.conj_ofReal]; push_cast; ring
  have he := H.unique hs
  convert he using 1
  apply integral_congr_ae; filter_upwards with z; simp only [map_mul]; ring

private theorem momentGamma_endpoint {a : ℝ} (ha : a∈Set.Ioo 0 1) (m : ℕ) :
    HasDerivAt (fun b => momentGamma a b m)
      (capCoeff a m/((m:ℝ)+1)*(psi ((m:ℝ)+2)-psi (2-a))) 0 := by
  let x := 2-a
  let y := (m:ℝ)+2
  have hx : 0<x := by dsimp [x]; linarith [ha.2]
  have hy : 0<y := by dsimp [y]; positivity
  have d (u : ℝ) (hu : 0<u) : HasDerivAt (fun b => Gamma (u-b)) (-(Gamma u*psi u)) 0 := by
    simpa only [sub_zero,id_eq,mul_neg_one,Function.comp_def] using
      ((show HasDerivAt Gamma (Gamma u*psi u) (u-0) by simpa using gamma_psi_derivative hu).comp 0 ((hasDerivAt_id (0:ℝ)).const_sub u))
  have hd := ((((d x hx).const_mul (Gamma y)).div ((d y hy).const_mul (Gamma x)) (by
    change Gamma x*Gamma (y-0)≠0; rw [sub_zero]; exact mul_ne_zero (Gamma_pos_of_pos hx).ne' (Gamma_pos_of_pos hy).ne')).const_mul (capCoeff a m/((m:ℝ)+1)))
  convert hd using 1
  · rfl
  · simp only [Pi.mul_apply,sub_zero]
    dsimp only [x,y] at *
    field_simp [(Gamma_pos_of_pos hx).ne',(Gamma_pos_of_pos hy).ne']; ring

/-- Every monomial moment of the physical disc input e_tau times conjugate(log(1-w)).
Multiplying this integral by m+1 gives the printed projection coefficient. -/
theorem discPower_log_moment {a : ℝ} (ha : a∈Set.Ioo 0 1) (m : ℕ) :
    (∫ z in disc, (discPower a z*conj (discLog z))*conj (z^m) ∂area) =
      ((capCoeff a m/((m:ℝ)+1)*(psi (2-a)-psi ((m:ℝ)+2)):ℝ):ℂ) := by
  let J := fun b : ℝ => ∫ z, conj (z^m)*discPower a z*conj (discPower b z) ∂discArea
  let G := fun b : ℝ => (momentGamma a b m:ℂ)
  have hm : Measurable (fun z : ℂ => conj (z^m)) := by fun_prop
  have hL := discPair_derivative_right (a:=a) (b:=0) (by linarith [ha.1]) (by linarith [ha.2]) hm (fun z hz => by
    have hnorm : ‖z‖<1 := by simpa [disc] using hz
    rw [Complex.norm_conj,norm_pow]
    exact (pow_le_one₀ (norm_nonneg _) hnorm.le).trans (by linarith [norm_nonneg (discLog z)]))
  have hR := (momentGamma_endpoint ha m).ofReal_comp
  have h0 : Tendsto (fun b : ℝ => b) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hrel : J =ᶠ[𝓝[>] (0:ℝ)] G := by
    filter_upwards [self_mem_nhdsWithin (s:=Set.Ioi 0) (a:=(0:ℝ)),h0.eventually_lt_const zero_lt_one] with b h1 h2
    exact discPower_shifted_pairing ha ⟨h1,h2⟩ m
  have hJ : Tendsto J (𝓝[>] (0:ℝ)) (𝓝 (J 0)) := hL.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hG : Tendsto G (𝓝[>] (0:ℝ)) (𝓝 (G 0)) := hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have eq0 := tendsto_nhds_unique (hJ.congr' hrel) hG
  have hwithin := hL.hasDerivWithinAt.congr_of_eventuallyEq hrel.symm eq0.symm
  have hid := (hwithin.derivWithin (uniqueDiffWithinAt_Ioi 0)).symm.trans (hR.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0))
  have he : (∫ z in disc, (discPower a z*conj (discLog z))*conj (z^m) ∂area) =
      -(∫ z, -conj (discLog z)*(conj (z^m)*discPower a z*conj (discPower 0 z)) ∂discArea) := by
    rw [←integral_neg]; apply integral_congr_ae; filter_upwards with z
    simp [discPower]; ring
  rw [he,hid]; push_cast; ring

end Liu
