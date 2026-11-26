import Challenge.QuotientDomain

/- Frozen input: Liu/Projection.lean -/
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

end Liu
end
