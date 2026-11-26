import Liu.FluxDecomposition

noncomputable section
open Set MeasureTheory Real
namespace Liu

/-- The convolution in Appendix E uses line measure dX/π and unnormalised dY. -/
def depthPoisson (u x : ℝ) (h : ℂ → ℂ) : ℂ :=
  (1/π:ℝ) • ∫ Y in Ioi u, ∫ X : ℝ, (poissonLine x (Y-u) X:ℂ)*h ⟨X,Y⟩

private theorem shifted_poisson {u x : ℝ} (h : ℂ → ℂ)
    (hi : Integrable (fun z : ℂ => ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*h (z+(u:ℂ)*Complex.I)) upperArea) :
    (∫ z, ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*h (z+(u:ℂ)*Complex.I) ∂upperArea) = depthPoisson u x h := by
  rw [upperArea_slices _ hi,depthPoisson]
  congr 1
  let F := fun Y : ℝ => ∫ X : ℝ, (poissonLine x (Y-u) X:ℂ)*h ⟨X,Y⟩
  have hp := (measurePreserving_add_right (volume:Measure ℝ) u).setIntegral_preimage_emb
    (Homeomorph.addRight u).measurableEmbedding F (Ioi u)
  have he : (fun y : ℝ => y+u) ⁻¹' Ioi u = Ioi 0 := by ext y; simp
  rw [he] at hp
  change _ = ∫ Y in Ioi u, F Y
  rw [←hp]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with X
  have hn : ‖(⟨X,y⟩:ℂ)-(x:ℂ)‖^2 = (X-x)^2+y^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]; simp [pow_two]
  have hz : (⟨X,y⟩:ℂ)+(u:ℂ)*Complex.I = ⟨X,y+u⟩ := by apply Complex.ext <;> simp
  simp only [F,poissonLine,add_sub_cancel_right,hn,hz]

theorem edgeCross_integrable {s γ u : ℝ} (hγ : γ ∈ Icc 0 (π/2)) (hu : 0<u) (x : ℝ) :
    Integrable (fun z : ℂ => ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*crossSource (normalMass s) (direction γ) (z+(u:ℂ)*Complex.I)) upperArea := by
  let p := normalPair s γ u hγ hu
  have ht := p.toPick.traceDensity_integrable x
  rw [show p.toPick.value = normalSum s γ u from normalPair_value ..] at ht
  have hi₁ := (isolatedDensity_integral p.ha₁ p.hw₁ x).1
  have hi₂ := (isolatedDensity_integral p.ha₂ p.hw₂ x).1
  apply (((ht.const_mul (-Complex.I)).sub (Complex.ofRealCLM.integrable_comp hi₁)).sub
    (Complex.ofRealCLM.integrable_comp hi₂)).congr
  exact ae_of_all _ (fun z => (trace_cross_identity s γ u x z).symm)

theorem crossTrace_is_convolution {s γ u : ℝ} (hγ : γ ∈ Icc 0 (π/2)) (hu : 0<u) (x : ℝ) :
    edgeCrossTrace s γ u x = depthPoisson u x (crossSource (normalMass s) (direction γ)) :=
  shifted_poisson _ (edgeCross_integrable hγ hu x)

theorem crossTrace_component {s γ u : ℝ} (hγ : γ ∈ Icc 0 (π/2)) (hu : 0<u) (x : ℝ) (L : ℂ →L[ℝ] ℝ) :
    ((L (edgeCrossTrace s γ u x)):ℂ) = depthPoisson u x (fun w => (L (crossSource (normalMass s) (direction γ) w):ℂ)) := by
  let h := crossSource (normalMass s) (direction γ)
  let F := fun z : ℂ => ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*h (z+(u:ℂ)*Complex.I)
  let T := Complex.ofRealCLM.comp L
  have hi : Integrable F upperArea := edgeCross_integrable hγ hu x
  have eqn (z : ℂ) : T (F z) =
      ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*(L (h (z+(u:ℂ)*Complex.I)):ℂ) := by
    dsimp [T,F]
    rw [←Complex.real_smul,map_smul]
    simp [smul_eq_mul]
  have hi' := T.integrable_comp hi
  change T (∫ z, F z ∂upperArea) = _
  rw [←T.integral_comp_comm hi]
  simp_rw [eqn]
  apply shifted_poisson (u:=u) (x:=x) (fun w => (L (h w):ℂ))
  exact hi'.congr (ae_of_all _ eqn)

theorem isolatedTrace_is_convolution (u x : ℝ) {w : ℂ} (hw : w.im<0) {m : ℝ} (hm : 0 < m) :
    depthPoisson u x (fun Z => ((m/‖Z-(w+(u:ℂ)*Complex.I)‖^2:ℝ):ℂ)) =
      ((m*isolatedTrace w.re (-w.im) x:ℝ):ℂ) := by
  obtain ⟨hi,he⟩ := isolatedDensity_integral hm hw x
  have eqn (z : ℂ) : ((z.im/‖z-(x:ℂ)‖^2:ℝ):ℂ)*
      ((m/‖(z+(u:ℂ)*Complex.I)-(w+(u:ℂ)*Complex.I)‖^2:ℝ):ℂ) = (isolatedDensity m w x z:ℂ) := by
    simp [isolatedDensity]
  rw [←shifted_poisson]
  · simp_rw [eqn,integral_complex_ofReal,he]
  · exact (Complex.ofRealCLM.integrable_comp hi).congr (ae_of_all _ (fun z => (eqn z).symm))

def depthPoissonReal (u x : ℝ) (h : ℂ → ℝ) : ℝ :=
  (1/π) * ∫ Y in Ioi u, ∫ X : ℝ, poissonLine x (Y-u) X*h ⟨X,Y⟩

theorem depthPoisson_ofReal (u x : ℝ) (h : ℂ → ℝ) :
    depthPoisson u x (fun w => (h w:ℂ)) = (depthPoissonReal u x h:ℂ) := by
  unfold depthPoisson depthPoissonReal
  simp only [Complex.real_smul,Complex.ofReal_mul]
  congr 1
  simp_rw [←Complex.ofReal_mul,integral_complex_ofReal]

theorem edge_trace_components {s γ u : ℝ} (hg : γ ∈ Icc 0 (π/2)) (hu : 0<u) (x : ℝ) :
    let H := crossSource (normalMass s) (direction γ)
    (edgeCrossTrace s γ u x).re = depthPoissonReal u x (fun w => (H w).re) ∧
      (edgeCrossTrace s γ u x).im = depthPoissonReal u x (fun w => (H w).im) := by
  have hr := crossTrace_component (s:=s) hg hu x Complex.reCLM
  have hi := crossTrace_component (s:=s) hg hu x Complex.imCLM
  rw [depthPoisson_ofReal] at hr hi
  exact ⟨Complex.ofReal_injective hr,Complex.ofReal_injective hi⟩

end Liu
