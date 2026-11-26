import Liu.ReciprocalTrace

noncomputable section
open Set Real MeasureTheory Metric
open scoped ComplexConjugate Topology
namespace Liu

/-- The real squared norms in the flux are continued by evaluating each
factor together with its Schwarz reflection in the separation parameter. -/
def topFluxIntegrand (s γ : ℝ) (w : ℂ) (x : ℝ) : ℂ :=
  let a := normalMass s
  let q := direction γ
  let Z := (x:ℂ)+Complex.I
  partnerTrace a q w x * conj (partnerTrace a q (conj w) x) -
    (k₀:ℂ)*topValue a q w Z*conj (topValue a q (conj w) Z)

def topFluxAnalytic (s γ : ℝ) (w : ℂ) : ℂ := (∫ x, topFluxIntegrand s γ w x)/(π:ℂ)

private theorem topFluxIntegrand_measurable (s γ : ℝ) (w : ℂ) :
    Measurable (topFluxIntegrand s γ w) := by
  letI : SFinite upperArea := by unfold upperArea area; infer_instance
  have hT (v : ℂ) : Measurable (fun x => partnerTrace (normalMass s) (direction γ) v x) := by
    have hm : Measurable (fun p : ℝ × ℂ => ((p.2.im/‖p.2-(p.1:ℂ)‖^2:ℝ):ℂ)*
        topRho (normalMass s) (direction γ) v (p.2+Complex.I)) := by
      unfold topRho topFactor topDerivFactor; fun_prop
    exact (hm.stronglyMeasurable.integral_prod_right' (ν:=upperArea)).measurable
  unfold topFluxIntegrand topValue topFactor
  fun_prop

private theorem reflected_disc_holo {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1)) :
    DifferentiableOn ℂ (fun w => conj (f (conj w))) (ball 0 1) := by
  intro w hw
  have hc : conj w∈ball (0:ℂ) 1 := by simpa using hw
  have h := (hf.differentiableAt (isOpen_ball.mem_nhds hc)).conj_conj
  simpa only [Complex.conj_conj,Function.comp_def] using h.differentiableWithinAt (s:=ball 0 1)

theorem topFluxAnalytic_holo (s γ : ℝ) : DifferentiableOn ℂ (topFluxAnalytic s γ) (ball 0 1) := by
  let a := normalMass s
  let q := direction γ
  have ha : 0≤a := (Certificate.normalMass_pos _).le
  have ha₁ : a≤1 := by dsimp [a]; linarith [Certificate.complement_normalMass s,Certificate.normalMass_pos (-s)]
  have hq : ‖q‖=1 := direction_norm _
  have hZ (x : ℝ) : 1≤‖(x:ℂ)+Complex.I‖ := by simpa using Complex.im_le_norm ((x:ℂ)+Complex.I)
  apply DifferentiableOn.div_const
  apply differentiableOn_disc_integral volume (fun w => (topFluxIntegrand_measurable s γ w).aestronglyMeasurable)
  · filter_upwards with x
    have hT := partnerTrace_differentiable ha ha₁ hq x
    have hV := (top_value_rho_differentiable ha ha₁ hq (hZ x)).1
    exact (hT.mul (reflected_disc_holo hT)).sub ((hV.const_mul (k₀:ℂ)).mul (reflected_disc_holo hV))
  · intro r hr hr₁
    let K := (1+r)/(1-r)
    let J := K*K*(1+1/(1-r)^2)
    have hK : 0≤K := by dsimp [K]; positivity
    have hJ : 0≤J := by dsimp [J]; positivity
    have hk : 0≤k₀ := by unfold k₀; positivity
    have hIso := isolatedTrace_memLp 0 zero_lt_one
    have hi := (memLp_two_iff_integrable_sq hIso.aestronglyMeasurable).mp hIso
    have hp := linePole_sq_integrable 0 zero_lt_one
    refine ⟨fun x => J^2*(isolatedTrace 0 1 x)^2+(k₀*K^2)*‖linePole 0 1 x‖^2,
      (hi.const_mul _).add (hp.const_mul _),?_⟩
    filter_upwards with x
    intro w hw
    have hb (v : ℂ) (hv : ‖v‖≤r) : ‖partnerTrace a q v x‖≤J*isolatedTrace 0 1 x :=
      partnerTrace_majorant ha ha₁ hr₁ hq hv x
    have hV (v : ℂ) (hv : ‖v‖≤r) : ‖topValue a q v ((x:ℂ)+Complex.I)‖≤K*‖linePole 0 1 x‖ := by
      apply ((top_rational_bounds ha ha₁ hr₁ hq (hZ x) hv).1).trans_eq
      simp [K,linePole,div_eq_mul_inv]
    have hw' : ‖conj w‖≤r := by simpa using hw
    have hI := isolatedTrace_nonneg 0 x zero_lt_one
    have h₁ := mul_le_mul (hb w hw) (hb _ hw') (norm_nonneg _) (mul_nonneg hJ hI)
    have h₂ := mul_le_mul (hV w hw) (hV _ hw') (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))
    unfold topFluxIntegrand
    apply (norm_sub_le ..).trans
    simp only [norm_mul,Complex.norm_conj,Complex.norm_of_nonneg hk]
    change ‖partnerTrace a q w x‖*‖partnerTrace a q (conj w) x‖+
      k₀*‖topValue a q w ((x:ℂ)+Complex.I)‖*‖topValue a q (conj w) ((x:ℂ)+Complex.I)‖≤_
    nlinarith only [h₁,mul_le_mul_of_nonneg_left h₂ hk]

theorem topFluxAnalytic_agrees {s γ v : ℝ} (hg : γ∈Icc 0 π) (hv : 0≤v) (hv₁ : v<1) :
    topFluxAnalytic s γ v=(boundaryFlux (unitDepthSum s γ v):ℂ) := by
  let S := unitDepthSum s γ v
  have he (x : ℝ) : topFluxIntegrand s γ v x=((‖field S x‖^2-k₀*‖S x‖^2:ℝ):ℂ) := by
    have hf := partnerTrace_actual (s:=s) hg hv hv₁ x
    have hV := (unitDepth_factors (s:=s) (γ:=γ) (z:=(x:ℂ)) (by simp) (by rwa [abs_of_nonneg hv])).1
    unfold topFluxIntegrand
    simp only [Complex.conj_ofReal,←hV]
    rw [mul_assoc (k₀:ℂ),Complex.mul_conj',Complex.mul_conj']
    simp only [S,hf,norm_neg,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow]
  unfold topFluxAnalytic boundaryFlux
  simp_rw [he,integral_complex_ofReal,Complex.ofReal_div]
  rfl

end Liu
