import Liu.InterpolationCharts

noncomputable section
open Set Real
open scoped ComplexConjugate
namespace Liu

/-- The printed upper partners, with the same continued mass as the lower
nodes, have the opposite exponential direction and base depth. -/
def CellLine.partnerTests (L : CellLine) (d v : ℂ → ℂ) (w : ℂ) : Prop :=
  let a := 1/(1+Complex.exp (L.s w))
  let p := -d w*Complex.I
  let q := v w*Complex.exp (-L.angle w*Complex.I)
  let p' := d w*Complex.I
  let q' := v w*Complex.exp (L.angle w*Complex.I)
  1+Complex.exp (L.s w) ≠ 0 ∧
    p.im<0 ∧ (p+q).im<0 ∧ (p+a*q).im<0 ∧
    0<p'.im ∧ 0<(p'+q').im ∧ 0<(p'+a*q').im

theorem CellLine.partner_tests_iff (L : CellLine) (d v : ℂ → ℂ)
    (hd : ∀ w, conj (d (conj w))=d w) (hv : ∀ w, conj (v (conj w))=v w) (w : ℂ) :
    w∈(L.nodes d v).domain L.massDomain ↔ L.partnerTests d v w := by
  let P := L.nodes d v
  let a := 1/(1+Complex.exp (L.s w))
  let p := -d w*Complex.I
  let q := v w*Complex.exp (-L.angle w*Complex.I)
  let p' := d w*Complex.I
  let q' := v w*Complex.exp (L.angle w*Complex.I)
  have hs : conj (L.s (conj w))=L.s w := by simp [CellLine.s]
  have hγ : conj (L.angle (conj w))=L.angle w := by
    cases h : L.logAngle <;> simp [CellLine.angle,h,←Complex.exp_conj]
  have hmass : conj (P.mass (conj w))=a := by simp [P,a,CellLine.nodes,←Complex.exp_conj,hs]
  have hd' : conj (1+Complex.exp (L.s (conj w)))=1+Complex.exp (L.s w) := by simp [←Complex.exp_conj,hs]
  have hD : conj w∈L.massDomain ↔ w∈L.massDomain := by
    change _ ≠ 0 ↔ _ ≠ 0
    rw [←hd']; exact (map_ne_zero_iff _ (starRingEnd ℂ).injective).symm
  have hL : conj (P.left (conj w))=p' := by simp [P,p',CellLine.nodes,hd]
  have hR : conj (P.right (conj w))=p'+q' := by simp [P,p',q',CellLine.nodes,←Complex.exp_conj,hd,hv,hγ]
  have hO : P.zeroNode w=p+a*q := by dsimp [P,PickChart.zeroNode,CellLine.nodes,p,a,q]; ring
  have hO' : conj (P.zeroNode (conj w))=p'+a*q' := by
    rw [PickChart.zeroNode,map_add,map_mul,map_mul,map_sub,map_one,hmass,hL,hR]; ring
  have im (z : ℂ) : z.im < 0 ↔ 0<(conj z).im := by simp
  have hB : P.below (conj w) ↔ 0<p'.im ∧ 0<(p'+q').im ∧ 0<(p'+a*q').im := by
    unfold PickChart.below
    rw [im (P.left _),im (P.right _),im (P.zeroNode _),hL,hR,hO']
  change ((w∈L.massDomain ∧ P.below w) ∧ conj w∈L.massDomain ∧ P.below (conj w)) ↔ _
  rw [hD,hB]
  change ((_ ∧ p.im<0 ∧ (p+q).im<0 ∧ (P.zeroNode w).im<0) ∧ _ ∧ _) ↔ _
  rw [hO]
  unfold CellLine.partnerTests
  change ((_ ∧ _ ∧ _ ∧ _) ∧ _ ∧ _) ↔ _
  tauto

theorem CellLine.cell_partner_tests (L : CellLine) (u : ℝ) (w : ℂ) :
    w∈(L.cellNodes u).domain L.massDomain ↔ L.partnerTests (L.depth u) (fun _ => 1) w :=
  L.partner_tests_iff _ _ (fun v => by simp [CellLine.depth,CellLine.y,←Complex.exp_conj]) (by simp) w

theorem CellLine.top_partner_tests (L : CellLine) (w : ℂ) :
    w∈L.topNodes.domain L.massDomain ↔ L.partnerTests (fun _ => 1) L.reciprocal w :=
  L.partner_tests_iff _ _ (by simp) (fun v => by simp [CellLine.reciprocal,CellLine.y]) w

end Liu
