module

public import Liu.DiscLogBound
public import Liu.GaussDerivatives

@[expose] public section

noncomputable section
open Set MeasureTheory Real Filter
open scoped Topology ComplexConjugate
namespace Liu

private theorem power_measurable (t : ℝ) : Measurable (discPower t) := by unfold discPower; fun_prop
private theorem log_measurable : Measurable discLog := by unfold discLog; fun_prop

private theorem discPair_derivative_left {a b : ℝ} (hab : 0<a+b) (hab2 : a+b<2)
    {q : ℂ → ℂ} (hm : Measurable q) (hq : ∀ z∈disc, ‖q z‖≤1+‖discLog z‖) :
    HasDerivAt (fun x => ∫ z, q z*discPower x z*conj (discPower b z) ∂discArea)
      (∫ z, -discLog z*(q z*discPower a z*conj (discPower b z)) ∂discArea) a := by
  let U := (a+2-b)/2
  have ha : a∈Ioo (-b) U := by dsimp [U]; constructor <;> linarith
  obtain ⟨B,hB,hdom⟩ := disc_log_domination (show U+b<2 by dsimp [U]; linarith)
  let F := fun x z => q z*discPower x z*conj (discPower b z)
  let F' := fun x z => -discLog z*F x z
  have hf (x : ℝ) : Measurable (F x) := (hm.mul (power_measurable x)).mul (Complex.continuous_conj.measurable.comp (power_measurable b))
  have hd (x : ℝ) : Measurable (F' x) := log_measurable.neg.mul (hf x)
  have he (z : ℂ) (hz : z∈disc) (x : ℝ) : ‖F x z‖ = ‖q z‖*‖1-z‖^(-(x+b)) := by
    dsimp only [F]; rw [norm_mul,norm_mul,Complex.norm_conj,discPower_norm,discPower_norm]
    have hn : 1-z≠0 := fun he => by rw [←sub_eq_zero.mp he] at hz; simpa [disc] using hz
    rw [neg_add_rev,rpow_add (norm_pos_iff.mpr hn)]; ring
  have point (z : ℂ) (hz : z∈disc) (x : ℝ) (hx : x∈Ioo (-b) U) :
      ‖F x z‖≤B z ∧ ‖F' x z‖≤B z := by
    have h := hdom z hz (x+b) ⟨by linarith [hx.1],by linarith [hx.2]⟩
    let L := ‖discLog z‖
    have hL : 0≤L := norm_nonneg _
    have hq' := hq z hz
    have hb' : ‖F x z‖≤‖1-z‖^(-(x+b))*(1+L) := by rw [he z hz x,mul_comm]; exact mul_le_mul_of_nonneg_left hq' (rpow_nonneg (norm_nonneg _) _)
    constructor
    · apply hb'.trans ((mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg L] : 1+L≤(1+L)^2) (by positivity)).trans h)
    · dsimp only [F']; rw [norm_mul,norm_neg]
      apply (mul_le_mul_of_nonneg_left hb' hL).trans
      change L*(‖1-z‖^(-(x+b))*(1+L))≤_
      apply le_trans _ h
      change _≤‖1-z‖^(-(x+b))*(1+L)^2
      rw [←mul_assoc,mul_comm L _,mul_assoc]
      exact mul_le_mul_of_nonneg_left (by nlinarith : L*(1+L)≤(1+L)^2) (by positivity)
  have hu : ∀ᵐ z ∂discArea, z∈disc := ae_restrict_mem Metric.isOpen_ball.measurableSet
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ:=discArea) (F:=F) (F':=F') (Ioo_mem_nhds ha.1 ha.2)
    (Eventually.of_forall fun x => (hf x).aestronglyMeasurable)
    (hB.mono' (hf a).aestronglyMeasurable (hu.mono fun z hz => (point z hz a ha).1))
    (hd a).aestronglyMeasurable (hu.mono fun z hz x hx => (point z hz x hx).2) hB ?_).2
  filter_upwards [hu] with z hz
  intro x _
  convert ((discPower_hasDerivAt x hz).const_mul (q z)).mul_const (conj (discPower b z)) using 1
  dsimp only [F',F]; ring

theorem discPair_derivative_right {a b : ℝ} (hab : 0<a+b) (hab2 : a+b<2)
    {q : ℂ → ℂ} (hm : Measurable q) (hq : ∀ z∈disc, ‖q z‖≤1+‖discLog z‖) :
    HasDerivAt (fun y => ∫ z, q z*discPower a z*conj (discPower y z) ∂discArea)
      (∫ z, -conj (discLog z)*(q z*discPower a z*conj (discPower b z)) ∂discArea) b := by
  have h := discPair_derivative_left (a:=b) (b:=a) (by linarith) (by linarith) (q:=fun z => conj (q z))
    (Complex.continuous_conj.measurable.comp hm) (fun z hz => by simpa using hq z hz)
  have hh := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt b h
  convert hh using 1
  · funext y; simp only [Function.comp_apply,ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply,←integral_conj]
    apply integral_congr_ae; filter_upwards with z; simp only [map_mul,Complex.conj_conj]; ring
  · simp only [ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply,←integral_conj]
    apply integral_congr_ae; filter_upwards with z; simp only [map_mul,map_neg,Complex.conj_conj]; ring

/-- The unprojected squared norm in the cap quotient, obtained by differentiating
the two-parameter integral on the physical disc. -/
theorem discPower_log_energy {a : ℝ} (ha : a∈Ioo 0 1) :
    (∫ z in disc, ‖discPower a z*conj (discLog z)‖^2 ∂area) =
      discGamma a a*(trigamma (2-a-a)+(psi (2-a)-psi (2-a-a))^2) := by
  have J (x y : ℝ) (hx : x∈Ioo 0 1) (hy : y∈Ioo 0 1) :
      (∫ z, discPower x z*conj (discPower y z) ∂discArea)=(discGamma x y:ℂ) :=
    discPower_pairing hx.1 hx.2 hy.1 hy.2
  have H (y : ℝ) (hy : y∈Ioo 0 1) :
      (∫ z, -discLog z*discPower a z*conj (discPower y z) ∂discArea) =
      ((discGamma a y*(psi (2-a)-psi (2-a-y)):ℝ):ℂ) := by
    have hh := discPair_derivative_left (a:=a) (b:=y) (by linarith [ha.1,hy.1]) (by linarith [ha.2,hy.2]) (q:=fun _ => 1) measurable_const
      (fun z _ => by simpa using norm_nonneg (discLog z))
    simp only [one_mul] at hh
    have hr := (discGamma_left (a:=a) (b:=y) (by linarith [ha.2,hy.2]) (by linarith [ha.2]) (by linarith [hy.2])).ofReal_comp
    have hl := hh.congr_of_eventuallyEq (by filter_upwards [Ioo_mem_nhds ha.1 ha.2] with x hx using (J x y hx hy).symm)
    simpa only [mul_assoc,Function.comp_def] using hl.unique hr
  have hh := discPair_derivative_right (a:=a) (b:=a) (by linarith [ha.1]) (by linarith [ha.2]) (q:=fun z => -discLog z) log_measurable.neg (fun z _ => by simp)
  have hr := (discGamma_mixed (a:=a) (b:=a) (by linarith [ha.2]) (by linarith [ha.2]) (by linarith [ha.2])).ofReal_comp
  have hl := hh.congr_of_eventuallyEq (by filter_upwards [Ioo_mem_nhds ha.1 ha.2] with y hy using (H y hy).symm)
  have eq := hl.unique hr
  apply Complex.ofReal_injective
  rw [←integral_complex_ofReal]
  apply Eq.trans _ (eq.trans (by push_cast; ring))
  apply integral_congr_ae; filter_upwards with z
  rw [Complex.ofReal_pow,←Complex.mul_conj']
  simp only [map_mul,Complex.conj_conj]; ring

end Liu
