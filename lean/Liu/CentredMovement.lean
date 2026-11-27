module

public import Liu.MovingLogTerms

@[expose] public section

noncomputable section
open Set Complex
namespace Liu

def massCentre (a b : ℂ) (P : Fin 3 → ℂ) := a*P 0+b*P 1

def movingNode (a b : ℂ) (P : Fin 3 → ℂ) (j : Fin 3) (t : ℂ) : ℂ :=
  massCentre a b P+t*(P j-massCentre a b P)

theorem movingNode_zero (a b : ℂ) (P : Fin 3 → ℂ) (j : Fin 3) :
    movingNode a b P j 0=massCentre a b P := by simp [movingNode]

theorem movingNode_one (a b : ℂ) (P : Fin 3 → ℂ) (j : Fin 3) : movingNode a b P j 1=P j := by simp [movingNode]

theorem movingNode_deriv (a b : ℂ) (P : Fin 3 → ℂ) (j : Fin 3) (t : ℂ) :
    HasDerivAt (movingNode a b P j) (P j-massCentre a b P) t := by
  change HasDerivAt (fun w : ℂ => massCentre a b P+w*(P j-massCentre a b P)) _ t
  simpa only [movingNode,id_eq,one_mul] using ((hasDerivAt_id t).mul_const (P j-massCentre a b P)).const_add (massCentre a b P)

private theorem mass_displacement (a b : ℂ) (hab : a+b=1) (P : Fin 3 → ℂ) :
    a*(P 0-massCentre a b P)+b*(P 1-massCentre a b P)=0 := by
  unfold massCentre
  linear_combination -(a*P 0+b*P 1)*hab

private theorem zero_displacement (a b : ℂ) (hab : a+b=1) (Q : Fin 3 → ℂ) (hQ : Q 2=a*Q 1+b*Q 0) :
    (Q 0-massCentre a b Q)+(Q 1-massCentre a b Q)-(Q 2-massCentre a b Q)=0 := by
  rw [hQ]; unfold massCentre
  linear_combination -(Q 0+Q 1)*hab

/-- At collision, differentiate the bivariate log term in the independent
pole and partner directions. The weighted pole velocities sum to zero.
The signed sum of partner velocities is zero as well. -/
theorem centred_field_deriv (s : Bool) (a b : ℂ) (hab : a+b=1) (P Q : Fin 3 → ℂ)
    (hQ : Q 2=a*Q 1+b*Q 0) (hp : orientedBelow s (massCentre a b P))
    (hq : orientedBelow (!s) (massCentre a b Q)) (x : ℝ) :
    HasDerivAt (fun t => tailSide s (fun i => movingNode a b P i t) (fun j => movingNode a b Q j t) a b x) 0 0 := by
  let p := massCentre a b P
  let q := massCentre a b Q
  let dp := fun i => P i-p
  let dq := fun j => Q j-q
  let F := fun k : ℂ × ℂ => tailTerm s k.1 k.2 (x:ℂ)
  let D := fderiv ℂ F (p,q)
  let X := D (1,0)
  let Y := D (0,1)
  have decomp (u v : ℂ) : D (u,v)=u*X+v*Y := by
    rw [show (u,v)=u • ((1,0):ℂ × ℂ)+v • ((0,1):ℂ × ℂ) by ext <;> simp]
    rw [map_add,map_smul,map_smul]; rfl
  have dF : HasFDerivAt F D (p,q) := (tailTerm_pair_diff s hp hq x).hasFDerivAt
  let T := fun i j t => tailTerm s (movingNode a b P i t) (movingNode a b Q j t) (x:ℂ)
  have Hd (i j : Fin 3) : HasDerivAt (T i j) (dp i*X+dq j*Y) 0 := by
    let A := fun t => (movingNode a b P i t,movingNode a b Q j t)
    have hA : HasDerivAt A (dp i,dq j) 0 := (movingNode_deriv a b P i 0).prodMk (movingNode_deriv a b Q j 0)
    have hB : HasFDerivAt F D (A 0) := by simpa [A,movingNode_zero,p,q] using dF
    simpa only [decomp,Function.comp_def,F,A,T] using hB.comp_hasDerivAt 0 hA
  let k := fieldCoefficient s
  have d₁ := (((Hd 0 0).const_mul k).const_mul a).add (((Hd 1 1).const_mul k).const_mul b)
  have d₂ := ((((Hd 0 1).sub (Hd 0 2)).const_mul a).add (((Hd 1 0).sub (Hd 1 2)).const_mul b)).const_mul k
  have hl : a*dp 0+b*dp 1=0 := mass_displacement a b hab P
  have hr : dq 0+dq 1-dq 2=0 := zero_displacement a b hab Q hQ
  convert d₁.add d₂ using 1
  · rfl
  · linear_combination -k*X*hl-k*Y*(a+b)*hr

theorem centred_pick_deriv (s : Bool) (a b : ℂ) (hab : a+b=1) (P : Fin 3 → ℂ)
    (hp : orientedBelow s (massCentre a b P)) (x : ℝ) :
    HasDerivAt (fun t => a*tailPole (movingNode a b P 0 t) x+b*tailPole (movingNode a b P 1 t) x) 0 0 := by
  let p := massCentre a b P
  let f := fun u : ℂ => tailPole u x
  have hn : (x:ℂ)-p≠0 := by
    intro e; have h := congrArg Complex.im (sub_eq_zero.mp e)
    cases s <;> simp [orientedBelow,p] at hp h <;> linarith
  have hd : DifferentiableAt ℂ f p := by dsimp [f,tailPole]; fun_prop (disch := assumption)
  have h (j : Fin 3) : HasDerivAt (fun t => f (movingNode a b P j t)) (deriv f p*(P j-p)) 0 := by
    have H : HasDerivAt f (deriv f p) (movingNode a b P j 0) := by simpa [movingNode_zero,p] using hd.hasDerivAt
    exact H.comp 0 (movingNode_deriv a b P j 0)
  convert ((h 0).const_mul a).add ((h 1).const_mul b) using 1
  linear_combination -deriv f p*(mass_displacement a b hab P)

end Liu
