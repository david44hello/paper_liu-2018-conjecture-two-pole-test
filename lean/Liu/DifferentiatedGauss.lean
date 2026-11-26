import Liu.GaussWeights
import Liu.GaussDerivatives

noncomputable section
open Set Real Filter
open scoped Topology
namespace Liu

private def gaussScore (a c : ℝ) := psi (c-2*a)-2*psi (c-a)

private theorem gaussValue_deriv {a c : ℝ} (ha : 0<a) (hc : 2*a<c) :
    HasDerivAt (gaussValue a) (gaussValue a c*gaussScore a c) c := by
  have x : 0<c-2*a := by linarith
  have y : 0<c-a := by linarith
  have hn := (gamma_psi_derivative x).comp c ((hasDerivAt_id c).sub_const (2*a))
  have hd := (gamma_psi_derivative y).comp c ((hasDerivAt_id c).sub_const a)
  have h := hn.div (hd.pow 2) (pow_ne_zero 2 (Gamma_pos_of_pos y).ne')
  convert h using 1
  · rfl
  · simp only [gaussValue,gaussScore,id_eq,Function.comp_apply,Pi.pow_apply,Nat.cast_ofNat]
    field_simp [(Gamma_pos_of_pos y).ne']; ring

private theorem gaussValue_second {a c : ℝ} (ha : 0<a) (hc : 2*a<c) :
    HasDerivAt (fun s => gaussValue a s*gaussScore a s)
      (gaussValue a c*(gaussScore a c^2+trigamma (c-2*a)-2*trigamma (c-a))) c := by
  have hp (u : ℝ) (h : u<c) : HasDerivAt (fun s => psi (s-u)) (trigamma (c-u)) c := by
    have hu : HasDerivAt psi (trigamma (c-u)) (c-u) := (hasDerivAt_psi_series (by linarith)).differentiableAt.hasDerivAt
    simpa only [mul_one,id_eq,Function.comp_def] using hu.comp c ((hasDerivAt_id c).sub_const u)
  have ds := (hp (2*a) hc).sub ((hp a (by linarith)).const_mul 2)
  convert (gaussValue_deriv ha hc).mul ds using 1
  · rfl
  · simp only [id_eq,gaussScore,Pi.sub_apply,Function.comp_apply]; ring

/-- Both differentiated Gauss sums with respect to their lower parameter.
The majorant is summable on an open interval about two. -/
theorem differentiated_gauss_at_two {a : ℝ} (ha : a∈Ioo 0 1) :
    HasSum (fun n : ℕ => -psi (2+n)*gaussWeight a n 2) (gaussValue a 2*gaussScore a 2) ∧
    HasSum (fun n : ℕ => (psi (2+n)^2-trigamma (2+n))*gaussWeight a n 2)
      (gaussValue a 2*(gaussScore a 2^2+trigamma (2-2*a)-2*trigamma (2-a))) := by
  obtain ⟨l,hl,h2,u,hu,hdom⟩ := gaussWeight_dominated ha
  let I := Ioo l 3
  have hmem : (2:ℝ)∈I := ⟨h2,by norm_num⟩
  have hc {c : ℝ} (h : c∈I) : 2*a<c := hl.trans h.1
  have pos {c : ℝ} (h : c∈I) : 0<c := by linarith [hc h,ha.1]
  let W := gaussWeight a
  let D := fun (n : ℕ) (c : ℝ) => -psi (c+n)*W n c
  let DD := fun (n : ℕ) (c : ℝ) => (psi (c+n)^2-trigamma (c+n))*W n c
  have hs {c : ℝ} (h : c∈I) := gaussWeight_sum ha.1 (hc h)
  have hd {c : ℝ} (h : c∈I) : Summable (fun n => D n c) := Summable.of_norm_bounded hu (fun n => by
    simpa only [D,W,Real.norm_eq_abs,neg_mul,abs_neg] using (hdom n c h).1)
  have hdd {c : ℝ} (h : c∈I) : Summable (fun n => DD n c) := Summable.of_norm_bounded hu (fun n => (hdom n c h).2)
  have H₁ {c : ℝ} (h : c∈I) : HasSum (fun n => D n c) (gaussValue a c*gaussScore a c) := by
    have dh := hasDerivAt_tsum_of_isPreconnected (t:=I) hu isOpen_Ioo (convex_Ioo _ _).isPreconnected
      (fun n y hy => gaussWeight_deriv (a:=a) (pos hy) n) (fun n y hy => by simpa only [Real.norm_eq_abs,neg_mul,abs_neg] using (hdom n y hy).1)
      h (hs h).summable h
    have e := dh.congr_of_eventuallyEq (f₁:=gaussValue a) (by filter_upwards [Ioo_mem_nhds h.1 h.2] with s hs' using (hs hs').tsum_eq.symm)
    have eq := e.unique (gaussValue_deriv ha.1 (hc h))
    exact eq ▸ (hd h).hasSum
  refine ⟨H₁ hmem,?_⟩
  have dh := hasDerivAt_tsum_of_isPreconnected (t:=I) hu isOpen_Ioo (convex_Ioo _ _).isPreconnected
    (fun n y hy => gaussWeight_second (a:=a) (pos hy) n) (fun n y hy => (hdom n y hy).2)
    hmem (hd hmem) hmem
  have e := dh.congr_of_eventuallyEq (f₁:=fun s => gaussValue a s*gaussScore a s) (by
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with s hs' using (H₁ hs').tsum_eq.symm)
  have eq := e.unique (gaussValue_second ha.1 (hc hmem))
  exact eq ▸ (hdd hmem).hasSum

private theorem gaussWeight_two (a : ℝ) (n : ℕ) : gaussWeight a n 2=(capCoeff a n)^2/((n:ℝ)+1) := by
  dsimp [gaussWeight,capCoeff]
  rw [show (2:ℝ)+n=((n+1:ℕ):ℝ)+1 by push_cast; ring,Gamma_nat_eq_factorial,Nat.factorial_succ]
  push_cast; field_simp

theorem projected_gauss_sum {a : ℝ} (ha : a∈Ioo 0 1) :
    (∑' n : ℕ, (capCoeff a n)^2/((n:ℝ)+1)*(psi (2-a)-psi ((n:ℝ)+2))^2) =
      gaussValue a 2*(trigamma (2-2*a)-2*trigamma (2-a)+(psi (2-a)-psi (2-2*a))^2)+capSigma (2-a) := by
  obtain ⟨h₁,h₂⟩ := differentiated_gauss_at_two ha
  have h₀ := gaussWeight_sum ha.1 (show 2*a<2 by linarith [ha.2])
  let A := psi (2-a)
  let T := fun n : ℕ => (capCoeff a n)^2*(trigamma ((n:ℝ)+2)/((n:ℝ)+1))
  have hT : Summable T := by
    apply Summable.of_nonneg_of_le _ (fun n => ?_) (by
      simpa using (summable_nat_add_iff 1).mpr ((summable_one_div_nat_pow (p:=2)).mpr (by decide)))
    · intro n; dsimp [T]; rw [trigamma_integer_tail]
      exact mul_nonneg (sq_nonneg _) (div_nonneg (tsum_nonneg fun j => by positivity) (by positivity))
    · have hc := capCoeff_endpoint_bound (t:=1-a) (show 1-a ∈ Icc (0:ℝ) 1 by constructor <;> linarith [ha.1,ha.2]) n
      rw [show 1-(1-a)=a by ring] at hc
      dsimp only [T]; rw [trigamma_integer_tail]
      apply (mul_le_mul (pow_le_one₀ hc.1 hc.2.1) (div_le_div_of_nonneg_right (reciprocal_square_tail n) (by positivity)) (by positivity) zero_le_one).trans_eq
      simp only [one_mul,one_div,div_eq_mul_inv,←sq,inv_pow]
  have h := (((h₀.mul_left (A^2)).add (h₁.mul_left (2*A))).add h₂).add hT.hasSum
  have eqT : (∑' n, T n)=capSigma (2-a) := by simp only [capSigma,show 2-(2-a)=a by ring,T]
  rw [eqT] at h
  apply Eq.trans _ (h.tsum_eq.trans (by dsimp only [gaussScore,A]; ring))
  apply tsum_congr; intro n
  dsimp only [Pi.add_apply,T,A]
  rw [gaussWeight_two,add_comm (2:ℝ) (n:ℝ)]; ring

end Liu
