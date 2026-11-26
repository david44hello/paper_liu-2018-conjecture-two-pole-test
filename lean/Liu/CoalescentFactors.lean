import Liu.SeparatedDomain

noncomputable section
open Set
open scoped Topology ComplexConjugate
namespace Liu.PickChart

/-- Complex separation along two independent velocities from a common pole. -/
def moving (a p l r : ℂ) : PickChart where
  mass _ := a
  left w := p+w*l
  right w := p+w*r

def velocity (a l r : ℂ) := a*l+(1-a)*r

theorem moving_regular (a p l r : ℂ) : (moving a p l r).Regular ((moving a p l r).domain univ) :=
  regular_domain _ isOpen_univ (differentiableOn_const _) (by unfold moving; fun_prop) (by unfold moving; fun_prop)

theorem moving_origin {a p l r : ℂ} (hp : p.im<0) : (0:ℂ)∈(moving a p l r).domain univ := by
  have hO : (moving a p l r).zeroNode 0 = p := by simp [zeroNode,moving]; ring
  have h : (moving a p l r).below 0 := by unfold below; rw [hO]; simp [moving,hp]
  exact ⟨⟨mem_univ _,h⟩,by simpa only [map_zero] using And.intro (mem_univ (0:ℂ)) h⟩

private theorem moving_node_deriv (p l z : ℂ) :
    HasDerivAt (fun w : ℂ => nodeFactor (p+w*l) z) (-l/(z+Complex.I)) 0 := by
  simpa [nodeFactor] using ((((hasDerivAt_id (0:ℂ)).mul_const l).const_add p).const_sub z).div_const (z+Complex.I)

/-- Both normalized factors have the same first derivative at collision.
Only the mass-weighted mean velocity occurs in it. -/
theorem moving_factors {a p l r z : ℂ} (hp : p.im<0) (hz : 0≤z.im) :
    let P := moving a p l r
    let B := nodeFactor p z
    let d := (velocity a l r/(z+Complex.I))/B^2
    P.valueFactor 0 z = B⁻¹ ∧ P.derivativeRatio 0 z = B⁻¹ ∧
    HasDerivAt (fun w => P.valueFactor w z) d 0 ∧ HasDerivAt (fun w => P.derivativeRatio w z) d 0 := by
  let P := moving a p l r
  let B := nodeFactor p z
  have hn : B≠0 := (nodeFactor_bounds hp hz).1
  have hZ : z+Complex.I ≠ 0 := by
    intro e; have he := congrArg Complex.im e; simp at he; linarith
  let u := (1-a)*l+a*r
  have hO (w : ℂ) : P.zeroNode w = p+w*u := by dsimp [P,moving,zeroNode,u]; ring
  have hL : HasDerivAt (fun w => nodeFactor (P.left w) z) (-l/(z+Complex.I)) 0 := moving_node_deriv p l z
  have hR : HasDerivAt (fun w => nodeFactor (P.right w) z) (-r/(z+Complex.I)) 0 := moving_node_deriv p r z
  have hN : HasDerivAt (fun w => nodeFactor (P.zeroNode w) z) (-u/(z+Complex.I)) 0 := by
    simp_rw [hO]; exact moving_node_deriv p u z
  have h₁ : nodeFactor (P.left 0) z=B := by simp [P,moving,B]
  have h₂ : nodeFactor (P.right 0) z=B := by simp [P,moving,B]
  have h₃ : nodeFactor (P.zeroNode 0) z=B := by simp [hO,B]
  have L := hL.inv (h₁ ▸ hn)
  have R := hR.inv (h₂ ▸ hn)
  have N := hN.inv (h₃ ▸ hn)
  change P.valueFactor 0 z=B⁻¹ ∧ P.derivativeRatio 0 z=B⁻¹ ∧ _ ∧ _
  refine ⟨?_,?_,?_,?_⟩
  · rw [valueFactor,h₁,h₂,h₃,mul_inv_cancel₀ hn,one_mul]
  · rw [derivativeRatio,h₁,h₂,h₃]; change a*B⁻¹*B*B⁻¹+(1-a)*B⁻¹*B*B⁻¹=B⁻¹
    field_simp [hn]; ring
  · change HasDerivAt (fun w => P.valueFactor w z) _ 0
    convert (hN.mul L).mul R using 1
    all_goals try rfl
    try simp only [Pi.inv_apply,Pi.mul_apply,h₁,h₂,h₃]
    change velocity a l r/(z+Complex.I)/B^2 = _
    dsimp only [u,velocity]
    field_simp [hn,hZ] <;> ring
  · change HasDerivAt (fun w => P.derivativeRatio w z) _ 0
    convert (((L.const_mul a).mul hR).mul N).add (((R.const_mul (1-a)).mul hL).mul N) using 1
    all_goals try rfl
    try simp only [Pi.inv_apply,Pi.mul_apply,h₁,h₂,h₃]
    change velocity a l r/(z+Complex.I)/B^2 = _
    dsimp only [u,velocity]
    field_simp [hn,hZ] <;> ring

end Liu.PickChart
