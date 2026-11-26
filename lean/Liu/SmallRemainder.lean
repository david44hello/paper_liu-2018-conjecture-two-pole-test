import Liu.BlendMajorant

noncomputable section
open Set Real MeasureTheory Filter
open scoped ComplexConjugate Topology
namespace Liu

theorem remainderMajorant_integral {q : ℂ} (hq : q.im≤0) {m d : ℝ} (hm : 0 < m)
    (hm' : m≤1/10) (hd : 0<d) :
    Integrable (fun z : ℂ => remainderMajorant m d ‖z-q‖) upperArea ∧
    (∫ z : ℂ, remainderMajorant m d ‖z-q‖ ∂upperArea) ≤ m^2*(445+70*log (1/m)) := by
  let a := 2*m*d
  let b := 2*d
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hab : a<b := by dsimp [a,b]; nlinarith [mul_le_mul_of_nonneg_right hm' hd.le]
  obtain ⟨i₁,v₁⟩ := radialDisc_majorant hq ha
  obtain ⟨i₂,v₂⟩ := radialInvDisc_majorant hq ha
  obtain ⟨i₃,v₃⟩ := radialInvAnnulus_majorant hq ha hab
  obtain ⟨i₄,v₄⟩ := radialInvTail_majorant hq hb (k:=4) (by decide)
  obtain ⟨i₅,v₅⟩ := radialInvTail_majorant hq hb (k:=3) (by decide)
  let c₁ := 115/d^2
  let c₂ := 80*m/d
  let c₃ := 70*m^2
  let c₄ := 49*m^2*d^2
  let c₅ := 95*m^2*d
  have i₁' := i₁.const_mul c₁
  have i₂' := i₂.const_mul c₂
  have i₃' := i₃.const_mul c₃
  have i₄' := i₄.const_mul c₄
  have i₅' := i₅.const_mul c₅
  refine ⟨(((i₁'.add i₂').add i₃').add i₄').add i₅',?_⟩
  unfold remainderMajorant
  erw [integral_add (((i₁'.add i₂').add i₃').add i₄') i₅',integral_add ((i₁'.add i₂').add i₃') i₄',
    integral_add (i₁'.add i₂') i₃',integral_add i₁' i₂']
  simp only [integral_const_mul]
  have H := add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left v₁ (show 0≤c₁ by dsimp [c₁]; positivity))
    (mul_le_mul_of_nonneg_left v₂ (show 0≤c₂ by dsimp [c₂]; positivity)))
    (mul_le_mul_of_nonneg_left v₃ (show 0≤c₃ by dsimp [c₃]; positivity)))
    (mul_le_mul_of_nonneg_left v₄ (show 0≤c₄ by dsimp [c₄]; positivity)))
    (mul_le_mul_of_nonneg_left v₅ (show 0≤c₅ by dsimp [c₅]; positivity))
  apply H.trans
  rw [show b/a=1/m by dsimp [a,b]; field_simp [hm.ne',hd.ne']]
  norm_num [Real.rpow_neg hb.le] 
  dsimp [c₁,c₂,c₃,c₄,c₅,a,b]
  field_simp [hd.ne']
  nlinarith only [sq_nonneg m,mul_nonneg (sq_nonneg m) (sq_nonneg d)]

def smallMassRemainder (p q : ℂ) (m : ℝ) : ℝ :=
  let A := pole 1 p
  let B := pole 1 q
  let g := fun z => blendedError (A z) ((m:ℂ)*B z)
  let Δ := fun z => g z-(m:ℂ)*linearBlend (A z) (B z)
  show ℝ from -2*(∫ z, field A z*conj (Δ z) ∂upperArea).re -
    (∫ z, ‖g z‖^2 ∂upperArea) - 2*m*(∫ z, field B z*conj (g z) ∂upperArea).re

/-- The lower bound on the actual three integrated terms of Appendix C.2. -/
theorem smallMassRemainder_estimates {p q : ℂ} (hp : p.im<0) (hq : q.im<0) {m : ℝ} (hm : 0 < m) (hm' : m≤1/10) :
    let A := pole 1 p
    let B := pole 1 q
    let g := fun z => blendedError (A z) ((m:ℂ)*B z)
    let Δ := fun z => g z-(m:ℂ)*linearBlend (A z) (B z)
    Integrable (fun z => field A z*conj (Δ z)) upperArea ∧
    Integrable (fun z => field B z*conj (g z)) upperArea ∧
    Integrable (fun z => ‖g z‖^2) upperArea ∧
    -(m^2*(520+111*log (2/m))) ≤ smallMassRemainder p q m := by
  let A := pole 1 p
  let B := pole 1 q
  let g := fun z => blendedError (A z) ((m:ℂ)*B z)
  let Δ := fun z => g z-(m:ℂ)*linearBlend (A z) (B z)
  let P := fun z => field A z*conj (Δ z)
  let Q := fun z => field B z*conj (g z)
  have hlog : 0≤log (2/m) := log_nonneg ((one_le_div hm).mpr (by linarith))
  by_cases e : p=q
  · subst q
    have hh : ∀ᵐ z ∂upperArea, g z=0 ∧ Δ z=0 := by
      filter_upwards [ae_restrict_mem (μ:=area) upper_open.measurableSet] with z hz
      have hpos := pole_im_pos zero_lt_one hp (show 0≤z.im from le_of_lt hz)
      have hn : A z≠0 := fun he => by change 0<(A z).im at hpos; simp [he] at hpos
      have hn' := Complex.ofReal_ne_zero.mpr hm.ne'
      have hq₁ : (m:ℂ)*A z/A z=(m:ℂ) := by field_simp [hn]
      have hq₂ : A z/((m:ℂ)*A z)=((m⁻¹:ℝ):ℂ) := by push_cast; field_simp [hn,hn']
      have harg {a : ℝ} (ha : 0<a) : (1+(a:ℂ)).arg=0 := by rw [←Complex.ofReal_one,←Complex.ofReal_add]; exact Complex.arg_ofReal_of_nonneg (by linarith)
      have hg0 : g z=0 := by change blendedError (A z) ((m:ℂ)*A z)=0; rw [blendedError,hq₁,hq₂,harg hm,harg (inv_pos.mpr hm)]; simp
      exact ⟨hg0,by change g z-(m:ℂ)*linearBlend (A z) (A z)=0; simp [linearBlend,hn,hg0]⟩
    have p0 : P=ᵐ[upperArea] 0 := by filter_upwards [hh] with z h; simp [P,h.2]
    have q0 : Q=ᵐ[upperArea] 0 := by filter_upwards [hh] with z h; simp [Q,h.1]
    have n0 : (fun z => ‖g z‖^2)=ᵐ[upperArea] 0 := by filter_upwards [hh] with z h; simp [h.1]
    refine ⟨(integrable_congr p0).mpr (integrable_zero _ _ _),(integrable_congr q0).mpr (integrable_zero _ _ _),
      (integrable_congr n0).mpr (integrable_zero _ _ _),?_⟩
    change _≤ -2*(∫ z, P z ∂upperArea).re-(∫ z, ‖g z‖^2 ∂upperArea)-2*m*(∫ z,Q z ∂upperArea).re
    rw [integral_congr_ae p0,integral_congr_ae q0,integral_congr_ae n0]
    simp; positivity
  let M := fun z => remainderMajorant m ‖p-q‖ ‖z-q‖
  obtain ⟨hM,hint⟩ := remainderMajorant_integral hq.le hm hm' (norm_pos_iff.mpr (sub_ne_zero.mpr e))
  have hμ : ∀ᵐ z ∂upperArea, z∈upper := ae_restrict_mem upper_open.measurableSet
  have hD : ∀ᵐ z ∂upperArea, 2*‖P z‖ + ‖g z‖^2 + (2*m)*‖Q z‖ ≤ M z := by
    filter_upwards [hμ] with z hz
    have h := remainderCost_le hp hq (le_of_lt hz) e hm hm'
    apply le_trans _ h
    change _ ≤ 5*‖A z‖*‖Δ z‖+‖g z‖^2+5*m*‖B z‖*‖g z‖
    simp only [P,Q,norm_mul,Complex.norm_conj]
    have hl := mul_le_mul_of_nonneg_right (onePole_field_bound hp (le_of_lt hz)) (norm_nonneg (Δ z))
    have hr := mul_le_mul_of_nonneg_right (onePole_field_bound hq (le_of_lt hz)) (norm_nonneg (g z))
    nlinarith only [hl,mul_le_mul_of_nonneg_left hr hm.le]
  have hg : Measurable g := by dsimp [g,blendedError,A,B,pole]; fun_prop
  have hΔ : Measurable Δ := by dsimp only [Δ]; apply hg.sub; dsimp [linearBlend,A,B,pole]; fun_prop
  have hP : Integrable P upperArea := by
    apply hM.mono' ((field_measurable A).mul (Complex.continuous_conj.measurable.comp hΔ)).aestronglyMeasurable
    filter_upwards [hD] with z h
    change ‖P z‖≤M z
    linarith [norm_nonneg (P z),sq_nonneg ‖g z‖,mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hm.le) (norm_nonneg (Q z))]
  have hQ : Integrable Q upperArea := by
    apply (hM.const_mul ((2*m)⁻¹)).mono' ((field_measurable B).mul (Complex.continuous_conj.measurable.comp hg)).aestronglyMeasurable
    filter_upwards [hD] with z h
    change ‖Q z‖≤(2*m)⁻¹*M z
    rw [inv_mul_eq_div]; apply (le_div_iff₀ (by positivity)).mpr
    linarith [norm_nonneg (P z),sq_nonneg ‖g z‖]
  have hg2 : Integrable (fun z => ‖g z‖^2) upperArea := by
    apply hM.mono' ((hg.norm.pow_const 2).aestronglyMeasurable)
    filter_upwards [hD] with z h
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    linarith [norm_nonneg (P z),mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hm.le) (norm_nonneg (Q z))]
  refine ⟨hP,hQ,hg2,?_⟩
  have hiP := Complex.reCLM.integrable_comp hP
  have hiQ := Complex.reCLM.integrable_comp hQ
  have hle : (∫ z, 2*(P z).re+‖g z‖^2+(2*m)*(Q z).re ∂upperArea)≤∫ z, M z ∂upperArea := by
    apply integral_mono_ae (((hiP.const_mul 2).add hg2).add (hiQ.const_mul (2*m))) hM
    filter_upwards [hD] with z h
    change 2*(P z).re+‖g z‖^2+(2*m)*(Q z).re≤M z
    exact (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (Complex.re_le_norm (P z)) (by norm_num : (0:ℝ)≤2)) (le_refl (‖g z‖^2)))
      (mul_le_mul_of_nonneg_left (Complex.re_le_norm (Q z)) (by positivity : 0≤2*m))).trans h
  erw [integral_add ((hiP.const_mul 2).add hg2) (hiQ.const_mul (2*m)),integral_add (hiP.const_mul 2) hg2,
    integral_const_mul,integral_const_mul,integral_re hP,integral_re hQ] at hle
  have hl : log (1/m)≤log (2/m) := log_le_log (by positivity) (by gcongr; norm_num)
  change _≤ -2*(∫ z, P z ∂upperArea).re-(∫ z, ‖g z‖^2 ∂upperArea)-2*m*(∫ z,Q z ∂upperArea).re
  have hk := mul_le_mul_of_nonneg_left (show 445+70*log (1/m)≤520+111*log (2/m) by linarith) (sq_nonneg m)
  change 2*(∫ z, P z ∂upperArea).re+(∫ z, ‖g z‖^2 ∂upperArea)+2*m*(∫ z, Q z ∂upperArea).re≤_ at hle
  linarith only [hle.trans hint,hk]

theorem smallMassRemainder_bound {p q : ℂ} (hp : p.im<0) (hq : q.im<0) {m : ℝ} (hm : 0 < m) (hm' : m≤1/10) :
    -(m^2*(520+111*log (2/m))) ≤ smallMassRemainder p q m :=
  (smallMassRemainder_estimates hp hq hm hm').2.2.2

end Liu
