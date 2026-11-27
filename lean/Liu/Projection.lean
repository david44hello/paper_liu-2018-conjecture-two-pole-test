module

public import Liu.QuotientDomain

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Liu

def representativeSubspace : Submodule ℂ PlaneL2 where
  carrier := analyticVectors
  zero_mem' := ⟨0,MemLp.zero,by fun_prop,rfl⟩
  add_mem' := by
    rintro _ _ ⟨f,hf,df,rfl⟩ ⟨g,hg,dg,rfl⟩
    exact ⟨f+g,hf.add hg,df.add dg,(MemLp.toLp_add hf hg).symm⟩
  smul_mem' := by
    rintro c _ ⟨f,hf,df,rfl⟩
    exact ⟨c • f,hf.const_smul c,df.const_smul c,(MemLp.toLp_const_smul c hf).symm⟩

theorem analytic_subspace_is_closure : analyticSubspace = representativeSubspace.topologicalClosure := by
  have h : Submodule.span ℂ analyticVectors = representativeSubspace :=
    Submodule.span_eq representativeSubspace
  rw [analyticSubspace,h]

theorem projection_range_of_closed (hc : IsClosed analyticVectors) :
    analyticSubspace = representativeSubspace :=
  analytic_subspace_is_closure.trans hc.submodule_topologicalClosure_eq

theorem asL2_add {f g : ℂ → ℂ} (hf : MemLp f 2 upperArea) (hg : MemLp g 2 upperArea) :
    asL2 (f+g) = asL2 f + asL2 g := by
  simp only [asL2,dif_pos (hf.add hg),dif_pos hf,dif_pos hg]
  rfl

theorem asL2_smul (c : ℂ) {f : ℂ → ℂ} (hf : MemLp f 2 upperArea) :
    asL2 (c • f) = c • asL2 f := by
  simp only [asL2,dif_pos (hf.const_smul c),dif_pos hf]
  rfl

theorem logInput_smul {c : ℂ} (hc : c ≠ 0) (f : ℂ → ℂ) :
    logInput (c • f) = c • logInput f + (c*(Real.log ‖c‖:ℂ)) • f := by
  funext z
  by_cases hz : f z = 0
  · simp [logInput,hz]
  · simp [logInput,norm_mul,Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hz),
      smul_eq_mul]
    ring

theorem quotient_smul {c : ℂ} (hc : c≠0) {f : ℂ → ℂ} (hf : MemLp f 2 upperArea)
    (hg : MemLp (logInput f) 2 upperArea) (hd : DifferentiableOn ℂ f upper)
    (hn : 0 < ‖asL2 f‖) : quotient (c • f) = quotient f := by
  have fix : project (asL2 f) = asL2 f := by
    simpa only [asL2,dif_pos hf] using project_fixes_analytic hf hd
  dsimp only [quotient]
  rw [logInput_smul hc,asL2_add (hg.const_smul c) (hf.const_smul _),
    asL2_smul c hg,asL2_smul _ hf,asL2_smul c hf, map_add,map_smul,map_smul,fix]
  rw [add_sub_add_right_eq_sub,←smul_sub,norm_smul,norm_smul]
  field_simp [hn.ne',norm_ne_zero_iff.mpr hc]

end Liu
