import Liu.Denominator

noncomputable section
open Filter Real
open scoped Topology
namespace Liu

theorem radial_mass_correction {m : ℝ} (hm : 0 < m) :
    Tendsto (fun ε : ℝ => (m^(2+2*ε)-m^2)/(2*ε)) (𝓝[>] 0) (𝓝 (m^2*log m)) := by
  have hd : HasDerivAt (fun ε : ℝ => 2+2*ε) 2 0 := by
    convert (((hasDerivAt_id (0:ℝ)).const_mul 2).const_add 2) using 1 <;> norm_num
  have h := (hd.const_rpow hm).tendsto_slope_zero_right.div_const 2
  simpa [smul_eq_mul,div_eq_mul_inv,mul_inv_rev,mul_comm,mul_left_comm,mul_assoc] using h

/-- The bounded-error expansion in the paragraph after Definition 2.1, with the
mass squared in the leading term exactly as printed. -/
theorem PickSum.energy_bounded_remainder {n : ℕ} (p : PickSum n) :
    ∃ B : ℝ, ∀ᶠ ε in 𝓝[>] (0:ℝ), |energy (p.power (1+ε))-p.mass^2/(2*ε)| ≤ B := by
  obtain ⟨C,hC⟩ := p.uniform_energy_error
  let M := |p.mass^2*log p.mass|+1
  have hb := (radial_mass_correction p.mass_pos).abs.eventually_lt_const
    (show |p.mass^2*log p.mass| < M by dsimp [M]; linarith)
  have e0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  refine ⟨C+M,?_⟩
  filter_upwards [hb,self_mem_nhdsWithin (a := (0:ℝ)) (s := Set.Ioi 0),
    e0.eventually_lt_const (show (0:ℝ)<1 by norm_num)] with ε hM he he'
  change 0 < ε at he
  have h := hC (2+2*ε) (by linarith) (by change ε < 1 at he'; linarith)
  rw [←p.power_energy he,show 2+2*ε-2=2*ε by ring] at h
  change |(p.mass^(2+2*ε)-p.mass^2)/(2*ε)| < M at hM
  calc
    _ = |(energy (p.power (1+ε))-p.mass^(2+2*ε)/(2*ε)) +
      ((p.mass^(2+2*ε)-p.mass^2)/(2*ε))| := by congr 1; ring
    _ ≤ _ := (abs_add_le ..).trans (add_le_add h hM.le)

end Liu
