module

public import Liu.MixedTrace

@[expose] public section

noncomputable section
open Set Real MeasureTheory
namespace Liu

theorem mixed_regular_norms {s γ u : ℝ} (hg : γ∈Icc 0 (π/2)) (hσ : 0<sin γ) (hu : 0<u) :
    let a := normalMass s
    let C := 8/(a*sin γ^4)
    let B := fun x => (1-a)*isolatedTrace (cos γ) (sin γ+u) x
    let c := edgeRealTrace s γ u
    let q := edgeImagTrace s γ u
    let H := mixedTrace s γ u
    (Integrable (fun x => B x^2) ∧ (∫ x, B x^2)/π≤C^2) ∧
    (Integrable (fun x => c x^2) ∧ (∫ x, c x^2)/π≤3*C^2) ∧
    (Integrable (fun x => q x^2) ∧ (∫ x, q x^2)/π≤4*C^2) ∧
    (Integrable (fun x => H x^2) ∧ (∫ x, H x^2)/π≤8*C^2) := by
  let a := normalMass s
  let b := 1-a
  let σ := sin γ
  let C := 8/(a*σ^4)
  let d := σ+u
  let B := fun x => b*isolatedTrace (cos γ) d x
  let c := edgeRealTrace s γ u
  let q := edgeImagTrace s γ u
  let H := mixedTrace s γ u
  have ha : 0<a := Certificate.normalMass_pos _
  have hb : 0<b := by dsimp [a,b]; rw [Certificate.complement_normalMass]; exact Certificate.normalMass_pos _
  have hσ₁ : σ≤1 := sin_le_one _
  have ha₁ : a≤1 := by dsimp [b] at hb; linarith
  have hb₁ : b≤1 := by dsimp [b]; linarith
  have hC₈ : 8≤C := (mixed_trace_controls (s:=s) hg hσ).1
  have hC : 0<C := by linarith
  have hd : 0<d := add_pos hσ hu
  have hD : 0<a*σ^4 := by positivity
  have hsmall : a*σ^4≤σ^3 := by
    nlinarith only [mul_le_mul_of_nonneg_right ha₁ (pow_nonneg hσ.le 4),
      mul_le_mul_of_nonneg_right hσ₁ (pow_nonneg hσ.le 3)]
  have hσ₃ : σ^3≤σ := by
    have hh := pow_le_pow_left₀ hσ.le hσ₁ 2
    nlinarith only [mul_le_mul_of_nonneg_right hh hσ.le]
  have hBC : k₀*b^2/d≤C^2 := by
    have hk : k₀≤2 := by unfold k₀; nlinarith [pow_le_pow_left₀ pi_pos.le pi_lt_four.le 2]
    have hn : k₀*b^2≤2 := by
      have hh := mul_le_mul hk (pow_le_pow_left₀ hb.le hb₁ 2) (sq_nonneg _) (by norm_num : (0:ℝ)≤2)
      simpa using hh
    calc
      _ ≤ 2/σ := div_le_div₀ (by norm_num) hn hσ (by dsimp [d]; linarith)
      _ ≤ C := by change 2/σ≤8/(a*σ^4); rw [div_le_div_iff₀ hσ hD]; linarith
      _ ≤ C^2 := by nlinarith [mul_le_mul_of_nonneg_right hC₈ hC.le]
  have hBmem : MemLp B 2 volume := (isolatedTrace_memLp (cos γ) hd).const_mul b
  have hBi := (memLp_two_iff_integrable_sq hBmem.aestronglyMeasurable).mp hBmem
  have hBn : (∫ x, B x^2)/π≤C^2 := by
    have he (x : ℝ) : B x^2=b^2*(isolatedTrace (cos γ) d x)^2 := mul_pow .. 
    simp_rw [he,integral_const_mul,mul_div_assoc,isolatedTrace_energy _ hd]
    exact (le_of_eq (by ring : b^2*(k₀/d)=k₀*b^2/d)).trans hBC
  obtain ⟨hci,hcn,hcs⟩ := edge_real_trace_fixed (s:=s) hg hσ hu.le
  have hcm : Measurable c := measurable_depthPoissonReal (Complex.measurable_re.comp (measurable_crossSource ..)) u
  have hcp (x : ℝ) : c x^2≤3*C*|c x| := by
    have hh := mul_le_mul_of_nonneg_right (hcs x) (abs_nonneg (c x))
    change |c x| *|c x|≤_ at hh
    simpa only [←sq,sq_abs] using hh
  have hcI : Integrable (fun x => c x^2) := (hci.abs.const_mul (3*C)).mono'
    (hcm.pow_const 2).aestronglyMeasurable (ae_of_all _ (fun x => (Real.norm_of_nonneg (sq_nonneg _)).le.trans (hcp x)))
  have hcN : (∫ x, c x^2)/π≤3*C^2 := by
    have hh := integral_mono_ae hcI (hci.abs.const_mul (3*C)) (ae_of_all _ hcp)
    rw [integral_const_mul] at hh
    apply (div_le_div_of_nonneg_right hh pi_pos.le).trans
    rw [mul_div_assoc]
    change (∫ x, |c x|)/π≤C at hcn
    nlinarith only [mul_le_mul_of_nonneg_left hcn hC.le]
  obtain ⟨hqm,hqn⟩ := edge_imag_trace_fixed (s:=s) hg hσ hu.le
  have hqI := (memLp_two_iff_integrable_sq hqm.aestronglyMeasurable).mp hqm
  have hcap : 16/σ^3≤2*C := by
    change 16/σ^3≤2*(8/(a*σ^4))
    rw [←mul_div_assoc,div_le_div_iff₀ (pow_pos hσ 3) hD]; linarith
  have hqN : (∫ x, q x^2)/π≤4*C^2 := hqn.trans ((pow_le_pow_left₀ (by positivity : 0≤16/σ^3) hcap 2).trans_eq (by ring))
  have hcmem := (memLp_two_iff_integrable_sq hcm.aestronglyMeasurable).mpr hcI
  have hHm : MemLp H 2 volume := hBmem.add hcmem
  have hHI := (memLp_two_iff_integrable_sq hHm.aestronglyMeasurable).mp hHm
  have hHN : (∫ x, H x^2)/π≤8*C^2 := by
    have hh (x : ℝ) : H x^2≤2*B x^2+2*c x^2 := by change (B x+c x)^2≤_; nlinarith [sq_nonneg (B x-c x)]
    have hi : Integrable (fun x => 2*B x^2+2*c x^2) := (hBi.const_mul _).add (hcI.const_mul _)
    have hv := integral_mono_ae hHI hi (ae_of_all _ hh)
    rw [integral_add (hBi.const_mul 2) (hcI.const_mul 2),integral_const_mul,integral_const_mul] at hv
    apply (div_le_div_of_nonneg_right hv pi_pos.le).trans
    rw [add_div,mul_div_assoc,mul_div_assoc]
    linarith
  exact ⟨⟨hBi,hBn⟩,⟨hcI,hcN⟩,⟨hqI,hqN⟩,⟨hHI,hHN⟩⟩

end Liu
