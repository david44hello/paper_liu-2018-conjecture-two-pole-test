import Liu.ReciprocalModel

noncomputable section
open Set Real MeasureTheory Metric
open scoped ComplexConjugate
namespace Liu

theorem top_value_rho_differentiable {a : ℝ} (ha : 0≤a) (ha₁ : a≤1) {q Z : ℂ}
    (hq : ‖q‖=1) (hZ : 1≤‖Z‖) :
    DifferentiableOn ℂ (fun w => topValue a q w Z) (ball 0 1) ∧
    DifferentiableOn ℂ (fun w => topRho a q w Z) (ball 0 1) := by
  have hZn : Z≠0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hZ)
  have hZb : conj Z≠0 := by simpa using hZn
  have hk (w : ℂ) (hw : w∈ball (0:ℂ) 1) :=
    top_factors ha ha₁ (show ‖w‖<1 by simpa using hw) (top_arg_bound (w:=w) hq hZ)
  have hj (w : ℂ) (hw : w∈ball (0:ℂ) 1) :=
    top_factors ha ha₁ (show ‖w‖<1 by simpa using hw)
      (top_arg_bound (q:=conj q) (Z:=conj Z) (w:=w) (by simpa using hq) (by simpa using hZ))
  constructor
  · intro w hw
    have hn := (hk w hw).1.1
    unfold topValue topFactor
    fun_prop (disch := assumption)
  · intro w hw
    have hn := (hk w hw).1.1
    have hn' := (hj w hw).1.1
    have hfac := (hj w hw).1.2
    have hA : DifferentiableAt ℂ (fun v => topFactor a (v*q/Z)) w := by unfold topFactor; fun_prop (disch := assumption)
    have hB : DifferentiableAt ℂ (fun v => topFactor a (v*conj q/conj Z)) w := by unfold topFactor; fun_prop (disch := assumption)
    have hD : DifferentiableAt ℂ (fun v => topDerivFactor a (v*conj q/conj Z)) w := by
      unfold topDerivFactor; fun_prop (disch := first | assumption | exact pow_ne_zero _ hn')
    exact ((((hA.div hB hfac).mul hD).div_const _).differentiableWithinAt)

/-- The rational continuation agrees with the true Pick value and
derivative at a real separation throughout the disc. -/
theorem unitDepth_factors {s γ v : ℝ} {z : ℂ} (hz : 0≤z.im) (hv : |v|<1) :
    let a := normalMass s
    let Z := z+Complex.I
    let q := direction γ
    let t := (v:ℂ)*q/Z
    unitDepthSum s γ v z=topValue a q v Z ∧
    deriv (unitDepthSum s γ v) z=topDerivFactor a t/Z^2 := by
  let a := normalMass s
  let Z := z+Complex.I
  let q := direction γ
  let t := (v:ℂ)*q/Z
  have hZ : 1≤‖Z‖ := (show 1≤Z.im by simp [Z]; linarith).trans (Complex.im_le_norm _)
  have hZn := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hZ)
  have h₁ : z≠ -Complex.I := by intro e; rw [e,Complex.neg_im,Complex.I_im] at hz; linarith
  have hn : ‖t‖<1 := (top_arg_bound (w:=(v:ℂ)) (direction_norm γ) hZ).trans_lt (by simpa using hv)
  have ht : 1-t≠0 := by intro e; rw [←sub_eq_zero.mp e] at hn; simp at hn
  have he : Z-(v:ℂ)*q=Z*(1-t) := by dsimp [t]; field_simp [hZn] <;> ring
  have hZn' : Z-(v:ℂ)*q≠0 := he ▸ mul_ne_zero hZn ht
  have h₂ : z≠ -Complex.I+(v:ℂ)*q := by
    intro e; apply hZn'; dsimp only [Z]; rw [e]; ring
  have d := (pole_hasDerivAt (a:=a) h₁).add (pole_hasDerivAt (a:=1-a) h₂)
  have hbase : z- -Complex.I=Z := by dsimp only [Z]; ring
  have hshift : z-(-Complex.I+(v:ℂ)*q)=Z*(1-t) := by rw [←he]; dsimp only [Z]; ring
  have htZ : t*Z=(v:ℂ)*q := div_mul_cancel₀ _ hZn
  constructor
  · change pole a (-Complex.I) z+pole (1-a) (-Complex.I+(v:ℂ)*q) z= -topFactor a t/Z
    simp only [pole,hbase,hshift,topFactor,Complex.ofReal_sub,Complex.ofReal_one]
    field_simp [hZn,ht] <;> ring
  · change deriv (pole a (-Complex.I)+pole (1-a) (-Complex.I+(v:ℂ)*q)) z=topDerivFactor a t/Z^2
    rw [d.deriv,hbase,hshift,topDerivFactor,Complex.ofReal_sub,Complex.ofReal_one]
    field_simp [hZn,ht] <;> ring

theorem unitDepth_source_partner {s γ v : ℝ} {z : ℂ} (hz : 0≤z.im) (hv : |v|<1) :
    source (unitDepthSum s γ v) z =
      (Complex.I/2)*topRho (normalMass s) (direction γ) v (z+Complex.I) := by
  let a := normalMass s
  let q := direction γ
  let Z := z+Complex.I
  let t := (v:ℂ)*q/Z
  let t' := (v:ℂ)*conj q/conj Z
  have hZ : 1≤‖Z‖ := (show 1≤Z.im by simp [Z]; linarith).trans (Complex.im_le_norm _)
  have hZn := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hZ)
  have hZb : conj Z≠0 := by simpa using hZn
  obtain ⟨hV,hD⟩ := unitDepth_factors (s:=s) (γ:=γ) hz hv
  have ht : conj t=t' := by simp [t,t']
  have hA : conj (topFactor a t)=topFactor a t' := by simp [topFactor,ht]
  have hB : conj (topDerivFactor a t)=topDerivFactor a t' := by simp [topDerivFactor,ht]
  have hn : topFactor a t'≠0 := (top_factors (Certificate.normalMass_pos s).le
    (by linarith [Certificate.complement_normalMass s,Certificate.normalMass_pos (-s)])
    hv ((top_arg_bound (q:=conj q) (Z:=conj Z) (w:=(v:ℂ)) (by simp [q,direction_norm]) (by simpa using hZ)).trans_eq (by simp))).1.2
  change unitDepthSum s γ v z= -topFactor a t/Z at hV
  change deriv (unitDepthSum s γ v) z=topDerivFactor a t/Z^2 at hD
  rw [source,hV,hD]
  change _=(Complex.I/2)*(topFactor a t/topFactor a t'*topDerivFactor a t'/((‖Z‖^2:ℝ):ℂ))
  rw [map_div₀,map_neg,hA,map_div₀,map_pow,hB,Complex.ofReal_pow,←Complex.mul_conj']
  field_simp [hZn,hZb,hn] <;> ring

end Liu
