import Mathlib

/- Frozen input: Liu/ChebyshevAlias.lean -/
noncomputable section
open Set Real Polynomial Polynomial.Chebyshev
namespace Liu

def firstKindAngle (n : ℕ) (j : Fin (n+1)) : ℝ :=
  (2*(j:ℝ)+1)*π/(2*((n:ℝ)+1))

def firstKindNode (n : ℕ) (j : Fin (n+1)) : ℂ := (cos (firstKindAngle n j):ℝ)

def firstKindInterpolant (n : ℕ) (f : ℂ → ℂ) : Polynomial ℂ :=
  Lagrange.interpolate Finset.univ (firstKindNode n) (fun j => f (firstKindNode n j))

end Liu
end
