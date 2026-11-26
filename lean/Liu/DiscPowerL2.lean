import Liu.DiscMonomials
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

noncomputable section
open Set MeasureTheory Real Filter Finset Metric
open scoped Topology ComplexConjugate InnerProductSpace
namespace Liu

abbrev discArea := area.restrict disc
abbrev DiscL2 := Lp ℂ 2 discArea

private theorem disc_monomial_memLp (n : ℕ) : MemLp (fun z : ℂ => z^n) 2 discArea := by
  have hm : Measurable (fun z : ℂ => z^n) := by fun_prop
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  letI : IsFiniteMeasureOnCompacts area := IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top
  exact ((show Continuous (fun z : ℂ => ‖z^n‖^2) by fun_prop).continuousOn.integrableOn_compact (μ:=area)
    (isCompact_closedBall (0:ℂ) 1)).mono_set ball_subset_closedBall

def discMonomial (n : ℕ) : DiscL2 := (disc_monomial_memLp n).toLp _
def discUnitMonomial (n : ℕ) : DiscL2 := ((√((n:ℝ)+1):ℝ):ℂ) • discMonomial n

theorem discUnitMonomial_orthonormal : Orthonormal ℂ discUnitMonomial := by
  rw [orthonormal_iff_ite]
  intro n m
  have h : inner ℂ (discMonomial n) (discMonomial m) = if m=n then ((m:ℂ)+1)⁻¹ else 0 := by
    rw [L2.inner_def,←disc_monomial_pairing]
    apply integral_congr_ae
    filter_upwards [(disc_monomial_memLp n).coeFn_toLp,(disc_monomial_memLp m).coeFn_toLp] with z hn hm
    change inner ℂ ((disc_monomial_memLp n).toLp _ z) ((disc_monomial_memLp m).toLp _ z) = _
    rw [hn,hm,RCLike.inner_apply]
  rw [discUnitMonomial,discUnitMonomial,inner_smul_left,inner_smul_right,h]
  by_cases he : n=m
  · subst m
    simp only [if_pos rfl,Complex.conj_ofReal]
    rw [←mul_assoc,←Complex.ofReal_mul,Real.mul_self_sqrt (by positivity : 0≤(n:ℝ)+1)]
    push_cast; field_simp
  · simp [he,Ne.symm he]

private def discCoeff (a : ℕ → ℂ) (n : ℕ) := a n/((√((n:ℝ)+1):ℝ):ℂ)

private theorem discCoeff_sq (a : ℕ → ℂ) (n : ℕ) : ‖discCoeff a n‖^2 = ‖a n‖^2/((n:ℝ)+1) := by
  simp [discCoeff,norm_div,div_pow,Real.sq_sqrt (by positivity : 0≤(n:ℝ)+1)]

private theorem disc_series_summable {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖^2/((n:ℝ)+1))) :
    Summable (fun n => discCoeff a n • discUnitMonomial n) := by
  have h : Summable (fun n => ‖discCoeff a n‖^2) := by simpa only [discCoeff_sq] using ha
  exact (discUnitMonomial_orthonormal.orthogonalFamily.summable_iff_norm_sq_summable (discCoeff a)).mpr h

/-- A power series with finite weighted coefficient energy converges in the
actual normalized disc L² space to its pointwise analytic sum. -/
theorem disc_series_L2 {a : ℕ → ℂ} {f : ℂ → ℂ}
    (ha : Summable (fun n => ‖a n‖^2/((n:ℝ)+1)))
    (hf : ∀ z ∈ disc, HasSum (fun n => a n*z^n) (f z)) :
    ∃ h : MemLp f 2 discArea, HasSum (fun n => discCoeff a n • discUnitMonomial n) (h.toLp f) := by
  let v := fun n => discCoeff a n • discUnitMonomial n
  let F := ∑' n, v n
  have hs : Summable v := disc_series_summable ha
  have ht : Tendsto (fun k : ℕ => ∑ n ∈ range k, v n) atTop (𝓝 F) := hs.hasSum.tendsto_sum_nat
  obtain ⟨ns,hns,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have he (n : ℕ) : (v n : ℂ → ℂ) =ᵐ[discArea] (fun z => a n*z^n) := by
    have hn : ((√((n:ℝ)+1):ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (sqrt_pos_of_pos (by positivity)))
    have hv : v n=a n • discMonomial n := by dsimp only [v,discUnitMonomial,discCoeff]; rw [smul_smul,div_mul_cancel₀ _ hn]
    rw [hv]
    filter_upwards [Lp.coeFn_smul (a n) (discMonomial n),(disc_monomial_memLp n).coeFn_toLp] with z h1 h2
    change _ = a n*z^n
    rw [h1,Pi.smul_apply,smul_eq_mul]; exact congrArg (a n*·) h2
  have hpart : ∀ᵐ z ∂discArea, ∀ k : ℕ, ((∑ n ∈ range k, v n : DiscL2) z)=∑ n ∈ range k, a n*z^n := by
    filter_upwards [ae_all_iff.mpr he,ae_all_iff.mpr (fun k => Lp.coeFn_fun_finsetSum (range k) v)] with z hz hsum
    intro k; rw [hsum k]; exact sum_congr rfl (fun n _ => hz n)
  have hF : F =ᵐ[discArea] f := by
    filter_upwards [hlim,hpart,ae_restrict_mem (μ:=area) isOpen_ball.measurableSet] with z hl hp hz
    simp only [hp] at hl
    exact tendsto_nhds_unique hl ((hf z hz).tendsto_sum_nat.comp hns.tendsto_atTop)
  have h := (memLp_congr_ae hF).mp (Lp.memLp F)
  refine ⟨h,?_⟩
  have hh : F=h.toLp f := Lp.ext (hF.trans h.coeFn_toLp.symm)
  exact hh ▸ hs.hasSum

/-- Parseval for two such analytic power series in normalized disc area. -/
theorem disc_series_pairing {a b : ℕ → ℂ} {f g : ℂ → ℂ}
    (ha : Summable (fun n => ‖a n‖^2/((n:ℝ)+1))) (hb : Summable (fun n => ‖b n‖^2/((n:ℝ)+1)))
    (hf : ∀ z ∈ disc, HasSum (fun n => a n*z^n) (f z)) (hg : ∀ z ∈ disc, HasSum (fun n => b n*z^n) (g z)) :
    HasSum (fun n => conj (a n)*b n/((n:ℂ)+1)) (∫ z in disc, g z*conj (f z) ∂area) := by
  obtain ⟨hF,h₁⟩ := disc_series_L2 ha hf
  obtain ⟨hG,h₂⟩ := disc_series_L2 hb hg
  have hn (n : ℕ) : conj (discCoeff a n)*discCoeff b n=conj (a n)*b n/((n:ℂ)+1) := by
    simp only [discCoeff,map_div₀,Complex.conj_ofReal,div_mul_div_comm,←Complex.ofReal_mul,
      Real.mul_self_sqrt (by positivity : 0≤(n:ℝ)+1),Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]
  have hi : inner ℂ (hF.toLp f) (hG.toLp g)=∫ z in disc, g z*conj (f z) ∂area := by
    rw [L2.inner_def]; apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp,hG.coeFn_toLp] with z h1 h2; rw [h1,h2,RCLike.inner_apply]
  rw [←hi]
  have hlim := Filter.Tendsto.inner (𝕜:=ℂ) h₁ h₂
  apply hlim.congr'
  filter_upwards with s
  exact (discUnitMonomial_orthonormal.inner_sum (discCoeff a) (discCoeff b) s).trans
    (sum_congr rfl (fun n _ => hn n))

end Liu
