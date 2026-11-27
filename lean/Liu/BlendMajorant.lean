module

public import Liu.BlendRegions
public import Liu.PoleArea

@[expose] public section

noncomputable section
open Set Real MeasureTheory
namespace Liu

def remainderCost (A B : ℂ) (m : ℝ) : ℝ :=
  let g := blendedError A ((m:ℂ)*B)
  let Δ := g-(m:ℂ)*linearBlend A B
  5*‖A‖*‖Δ‖+‖g‖^2+5*m*‖B‖*‖g‖

def remainderMajorant (m d r : ℝ) :=
  115/d^2*radialDisc (2*m*d) r + 80*m/d*radialInvDisc (2*m*d) r +
  70*m^2*radialInvAnnulus (2*m*d) (2*d) r +
  49*m^2*d^2*radialInvTail 4 (2*d) r + 95*m^2*d*radialInvTail 3 (2*d) r

private theorem pole_norm_unit (w z : ℂ) : ‖pole 1 w z‖=1/‖z-w‖ := by simp [pole,norm_div]

theorem remainderCost_le {p q z : ℂ} (hp : p.im<0) (hq : q.im<0) (hz : 0≤z.im)
    (hpq : p≠q) {m : ℝ} (hm : 0 < m) (hm' : m≤1/10) :
    remainderCost (pole 1 p z) (pole 1 q z) m ≤ remainderMajorant m ‖p-q‖ ‖z-q‖ := by
  let A := pole 1 p z
  let B := pole 1 q z
  let g := blendedError A ((m:ℂ)*B)
  let Δ := g-(m:ℂ)*linearBlend A B
  let r := ‖z-q‖
  let R := ‖z-p‖
  let d := ‖p-q‖
  have hn {w : ℂ} (hw : w.im<0) : z-w≠0 := sub_ne_zero.mpr fun e => by rw [e] at hz; linarith
  have hr : 0<r := norm_pos_iff.mpr (hn hq)
  have hR : 0<R := norm_pos_iff.mpr (hn hp)
  have hd : 0<d := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
  have hA : A∈upper := pole_im_pos zero_lt_one hp hz
  have hB : B∈upper := pole_im_pos zero_lt_one hq hz
  have ha : ‖A‖=1/R := pole_norm_unit .. 
  have hb : ‖B‖=1/r := pole_norm_unit ..
  have hAn := norm_pos_iff.mp (ha.symm ▸ one_div_pos.mpr hR)
  have hBn := norm_pos_iff.mp (hb.symm ▸ one_div_pos.mpr hr)
  have hBm := mul_ne_zero (Complex.ofReal_ne_zero.mpr hm.ne') hBn
  have hg5 := blendedError_bound hAn hBm
  rw [norm_mul,Complex.norm_of_nonneg hm.le] at hg5
  have hmin := hg5.trans (mul_le_mul_of_nonneg_right (by linarith [pi_lt_d2] : 3*π/2≤5) (le_min (by positivity) (norm_nonneg _)))
  have hgA : ‖g‖≤5*‖A‖ := hmin.trans (mul_le_mul_of_nonneg_left (min_le_right ..) (by norm_num))
  have hgB : ‖g‖≤5*m*‖B‖ := (hmin.trans (mul_le_mul_of_nonneg_left (min_le_left ..) (by norm_num))).trans_eq (by ring)
  have tri₁ : d≤R+r := by simpa [d,R,r,norm_sub_rev p z] using norm_sub_le_norm_sub_add_norm_sub p z q
  have tri₂ : r≤R+d := norm_sub_le_norm_sub_add_norm_sub z p q
  have tri₃ : R≤r+d := by simpa [d,R,r,norm_sub_rev q p] using norm_sub_le_norm_sub_add_norm_sub z q p
  change 5*‖A‖*‖Δ‖+‖g‖^2+5*m*‖B‖*‖g‖ ≤ remainderMajorant m d r
  by_cases hs : r≤2*m*d
  · have hlo : 2*d/3≤R := by nlinarith [mul_le_mul_of_nonneg_right hm' hd.le]
    have ha' : ‖A‖≤1.5/d := by rw [ha,div_le_div_iff₀ hR hd]; linarith
    have hg : ‖g‖≤7.5/d := hgA.trans ((mul_le_mul_of_nonneg_left ha' (by norm_num : 0≤(5:ℝ))).trans_eq (by ring))
    have hΔ : ‖Δ‖≤7.5/d+5*m/r := by
      apply (norm_sub_le ..).trans (add_le_add hg _)
      rw [norm_mul,Complex.norm_of_nonneg hm.le]
      exact (mul_le_mul_of_nonneg_left (linearBlend_bound hA hB) hm.le).trans_eq (by rw [hb]; ring)
    have hrle : r≤2*d := by nlinarith [mul_le_mul_of_nonneg_right hm' hd.le]
    simp only [remainderMajorant,radialDisc,radialInvDisc,radialInvAnnulus,radialInvTail,
      if_pos hs,indicator_of_notMem (show r∉Ioc (2*m*d) (2*d) from fun h => (not_lt.mpr hs) h.1),
      indicator_of_notMem (show r∉Ioi (2*d) from not_lt.mpr hrle),mul_zero,add_zero,mul_one]
    have H := mul_le_mul ha' hΔ (norm_nonneg _) (by positivity)
    have G := pow_le_pow_left₀ (norm_nonneg _) hg 2
    have T := mul_le_mul_of_nonneg_left hg (show 0≤ m*‖B‖ by positivity)
    rw [hb] at T ⊢
    have hpos : 0≤(d^2)⁻¹ := by positivity
    have hpos' : 0≤ m*d⁻¹*r⁻¹ := by positivity
    simp only [div_eq_mul_inv,←inv_pow,mul_add] at H G T ⊢
    nlinarith only [H,G,T,hpos,hpos']
  have hsm : 2*m*d<r := lt_of_not_ge hs
  by_cases hmid : r≤2*d
  · have hξ : ‖(m:ℂ)*B/A‖≤3/5 := by
      rw [norm_div,norm_mul,Complex.norm_of_nonneg hm.le,hb,ha,div_div_eq_mul_div,div_one]
      have hmr := mul_le_mul_of_nonneg_left tri₃ hm.le
      have hmp := mul_le_mul_of_nonneg_right hm' hr.le
      apply (le_of_mul_le_mul_right (a:=r) _ hr)
      field_simp [hr.ne'] <;> nlinarith
    have hΔ := blend_remainder_near hA hB hm hξ
    change ‖A‖*‖Δ‖≤_ at hΔ
    simp only [remainderMajorant,radialDisc,radialInvDisc,radialInvAnnulus,radialInvTail,if_neg hs,
      indicator_of_mem (show r∈Ioc (2*m*d) (2*d) from ⟨hsm,hmid⟩),
      indicator_of_notMem (show r∉Ioi (2*d) from not_lt.mpr hmid),mul_zero,zero_add,add_zero]
    have hG := pow_le_pow_left₀ (norm_nonneg g) hgB 2
    have hT := mul_le_mul_of_nonneg_left hgB (show 0≤ m*‖B‖ by positivity)
    rw [hb] at hΔ hG hT ⊢
    simp only [one_div,←inv_pow] at hΔ hG hT ⊢
    nlinarith only [hΔ,hG,hT]
  · have hfar : 2*d<r := lt_of_not_ge hmid
    let e := (q-p)/(z-q)
    have he : B/A=1+e := by dsimp [A,B,pole,e]; push_cast; field_simp [hn hp,hn hq]; ring
    have hen : ‖e‖=d/r := by dsimp [e,r,d]; rw [norm_div,norm_sub_rev q p]
    have hAB : ‖A‖≤2*‖B‖ := by rw [ha,hb,←mul_div_assoc,mul_one,div_le_div_iff₀ hR hr]; linarith
    obtain ⟨hg,hΔ⟩ := blend_far_bounds hA hB hm hm' he (by rw [hen,div_le_iff₀ hr]; linarith) hAB
    change ‖g‖≤_ at hg
    change ‖Δ‖≤_ at hΔ
    have H := mul_le_mul hAB hΔ (norm_nonneg _) (by positivity)
    have G := pow_le_pow_left₀ (norm_nonneg g) hg 2
    have T := mul_le_mul_of_nonneg_left hg (show 0≤ m*‖B‖ by positivity)
    simp only [remainderMajorant,radialDisc,radialInvDisc,radialInvAnnulus,radialInvTail,if_neg hs,
      indicator_of_notMem (show r∉Ioc (2*m*d) (2*d) from fun h => hmid h.2),
      indicator_of_mem (show r∈Ioi (2*d) from hfar),mul_zero,zero_add,add_zero]
    rw [hb,hen] at H G T
    rw [hb]
    simp only [div_eq_mul_inv,one_mul,←inv_pow] at H G T ⊢
    nlinarith only [H,G,T]

end Liu
