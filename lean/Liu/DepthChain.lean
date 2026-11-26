import Liu.ReciprocalTail

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace Liu

private theorem position_in_chain (v : ℕ → ℝ) (n : ℕ) {u : ℝ} (h : v 0 ≤ u) :
    v n ≤ u ∨ ∃ k < n, v k ≤ u ∧ u ≤ v (k+1) := by
  induction n with
  | zero => exact Or.inl h
  | succ n ih =>
    rcases ih with hlast | ⟨k,hk,hx⟩
    · by_cases hn : v (n+1) ≤ u
      · exact Or.inl hn
      · exact Or.inr ⟨n,Nat.lt_succ_self _,hlast,le_of_not_ge hn⟩
    · exact Or.inr ⟨k,Nat.lt_succ_of_lt hk,hx⟩

/-- The signed depth-chain criterion of Lemma 6.3. There are n finite intervals followed by
the unbounded top interval. Its tail is explicitly integrable and every partial cell, including
every interior point of the top interval, is tested. -/
theorem depth_chain_criterion {s γ b : ℝ} (hg : γ ∈ Icc 0 (Real.pi/2))
    (cluster : deepCluster) (hf : Certificate.fluxIdentity)
    (v : ℕ → ℝ) (n : ℕ) (hv : ∀ k, 0 < v k) (inc : Monotone v)
    (htail : ∀ t : ℝ, v n ≤ t → IntegrableOn (flux s γ) (Ioi t))
    (top : ∀ t : ℝ, v n ≤ t → (∫ x in Ioi t, flux s γ x) < singleConstant-k₀)
    (cells : ∀ k < n, ∀ t ∈ Icc (v k) (v (k+1)),
      (∫ x in t..v (k+1),flux s γ x) +
        (∑ j ∈ Finset.Ico (k+1) n, ∫ x in v j..v (j+1),flux s γ x) +
        (∫ x in Ioi (v n),flux s γ x) < singleConstant-k₀)
    (endpoint : b ≤ (singleConstant-k₀) - ((∑ j ∈ Finset.Ico 0 n, ∫ x in v j..v (j+1),flux s γ x) +
        ∫ x in Ioi (v n),flux s γ x)) :
    (∀ t : ℝ, v 0 ≤ t → 0 < margin s γ t) ∧ b ≤ margin s γ (v 0) := by
  have ct (t : ℝ) (ht : v n ≤ t) :=
    intervalIntegral_tendsto_integral_Ioi t (htail t ht) tendsto_id
  have hseg (k : ℕ) := (hf s γ hg (v k) (v (k+1)) (hv k) (inc (Nat.le_succ _))).1
  have htop (T : ℝ) (hT : v n ≤ T) := (hf s γ hg (v n) T (hv n) hT).1
  constructor
  · intro t ht
    have hp := (hv 0).trans_le ht
    rcases position_in_chain v n ht with hn | ⟨k,hk,hl,hr⟩
    · have hh := anchor_of_cluster_and_flux cluster hf hg hp (ct t hn)
      linarith [top t hn]
    · have ht₁ := (hf s γ hg t (v (k+1)) hp hr).1
      have hc := chain_suffix_limit (nodes := v) (Nat.succ_le_of_lt hk) ht₁
        (fun j _ => hseg j) htop (ct (v n) le_rfl)
      have ha := anchor_of_cluster_and_flux cluster hf hg hp hc
      linarith [cells k hk t ⟨hl,hr⟩]
  · have hc := chain_suffix_limit (nodes := v) (u := v 0) (Nat.zero_le n) (IntervalIntegrable.refl)
      (fun j _ => hseg j) htop (ct (v n) le_rfl)
    have ha := anchor_of_cluster_and_flux cluster hf hg (hv 0) hc
    simp only [intervalIntegral.integral_same,zero_add] at ha
    exact endpoint.trans ha

end Liu
