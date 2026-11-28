import Ordinary

/-!
Finite discrepancy bounds for progression-free extremizers.
The imported profile theorem and supporting chain are by Deldor14, pinned at
fa1c1438d116bda45b4cdbc272bbf41a96feed73.
-/

namespace Erdos142Equidistribution

open Set.IsAPOfLengthFree ProgressionParity
open Filter Topology

theorem interval_count_le {k a b : ℕ} (hk : 1 < k) (S : Finset ℕ)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) :
    (S.filter (fun x => a < x ∧ x ≤ b)).card ≤ maxCard k (b-a) := by
  let H := S.filter (fun x => a < x ∧ x ≤ b)
  let T := H.image (·-a)
  have tc : T.card = H.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy eq
    have xl := (Finset.mem_filter.mp hx).2.1
    have yl := (Finset.mem_filter.mp hy).2.1
    change x-a = y-a at eq
    omega
  have hc : T.card ≤ maxCard k (b-a) := by
    apply bound_witness hk
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨_,low,high⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    · intro c d hd run
      apply (upstream_iff_free (S : Set ℕ) hk).mp hf (c+a) d hd
      apply (run_iff_forall _ _ _ _).mpr
      intro i hi
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp ((run_iff_forall _ _ _ _).mp run i hi)
      obtain ⟨sx,low,_⟩ := Finset.mem_filter.mp hx
      change x-a = c+i*d at eq
      rwa [show c+a+i*d=x by omega]
  rwa [tc] at hc

theorem prefix_count_le {k N x : ℕ} (hk : 1 < k) (S : Finset ℕ)
    (hs : S ⊆ Finset.Icc 1 N) (hf : (S : Set ℕ).IsAPOfLengthFree k) :
    (S.filter (· ≤ x)).card ≤ maxCard k x := by
  have eq : S.filter (fun y => 0 < y ∧ y ≤ x) = S.filter (· ≤ x) := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · exact fun ⟨hy,_,hxy⟩ => ⟨hy,hxy⟩
    · intro ⟨hy,hxy⟩
      exact ⟨hy,(Finset.mem_Icc.mp (hs hy)).1,hxy⟩
  simpa only [Nat.sub_zero,eq] using interval_count_le hk S hf (a := 0) (b := x)

theorem tail_count_le {k N x : ℕ} (hk : 1 < k) (S : Finset ℕ)
    (hs : S ⊆ Finset.Icc 1 N) (hf : (S : Set ℕ).IsAPOfLengthFree k) :
    (S.filter (fun y => ¬ y ≤ x)).card ≤ maxCard k (N-x) := by
  have eq : S.filter (fun y => x < y ∧ y ≤ N) = S.filter (fun y => ¬ y ≤ x) := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · exact fun ⟨hy,hxy,_⟩ => ⟨hy,by omega⟩
    · intro ⟨hy,hxy⟩
      exact ⟨hy,by omega,(Finset.mem_Icc.mp (hs hy)).2⟩
  simpa only [eq] using interval_count_le hk S hf (a := x) (b := N)

lemma max_card_pos {k N : ℕ} (hk : 3 ≤ k) (hN : 0 < N) :
    0 < (maxCard k N : ℝ) := by
  have lower := interval_mono (by omega : 1<k) (show 1≤N from hN)
  rw [(initial_values (by omega : 1<k)).1 1 (by omega)] at lower
  exact_mod_cast (show 0 < maxCard k N by omega)

/-- Every near-extremizer has a small prefix discrepancy whenever the extremal
cardinality profile is close to linear. The normalization is by the optimum. -/
theorem prefix_discrepancy {k N x : ℕ} (hk : 3 ≤ k) (hN : 0 < N)
    (hx : x ≤ N) (S : Finset ℕ) (hs : S ⊆ Finset.Icc 1 N)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) {ε δ : ℝ} (hδ : 0 ≤ δ)
    (near : (1-δ)*(maxCard k N : ℝ) ≤ S.card)
    (profile : ∀ y ≤ N, |(maxCard k y : ℝ)/maxCard k N-(y:ℝ)/N| ≤ ε) :
    |((S.filter (· ≤ x)).card : ℝ)/maxCard k N-(x:ℝ)/N| ≤ ε+δ := by
  have rp := max_card_pos hk hN
  have np : 0 < (N : ℝ) := by exact_mod_cast hN
  have left : ((S.filter (· ≤ x)).card : ℝ) ≤ maxCard k x := by
    exact_mod_cast prefix_count_le (by omega : 1<k) S hs hf
  have right : ((S.filter (fun y => ¬ y ≤ x)).card : ℝ) ≤ maxCard k (N-x) := by
    exact_mod_cast tail_count_le (by omega : 1<k) S hs hf
  have sum : ((S.filter (· ≤ x)).card : ℝ)+((S.filter (fun y => ¬ y ≤ x)).card : ℝ) = S.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := S) (p := (· ≤ x)))
  have lu := (div_le_div_of_nonneg_right left rp.le).trans
    (by linarith [(abs_le.mp (profile x hx)).2] : (maxCard k x:ℝ)/maxCard k N ≤ (x:ℝ)/N+ε)
  have ru := (div_le_div_of_nonneg_right right rp.le).trans
    (by linarith [(abs_le.mp (profile (N-x) (Nat.sub_le _ _))).2] :
      (maxCard k (N-x):ℝ)/maxCard k N ≤ ((N-x:ℕ):ℝ)/N+ε)
  rw [Nat.cast_sub hx,sub_div,div_self np.ne'] at ru
  have low : 1-δ ≤ (S.card : ℝ)/maxCard k N := (le_div_iff₀ rp).mpr near
  have sum' := congrArg (fun t : ℝ => t / maxCard k N) sum
  rw [add_div] at sum'
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The same profile condition controls every interval, simultaneously for all
near-extremizers. -/
theorem interval_discrepancy {k N a b : ℕ} (hk : 3 ≤ k) (hN : 0 < N)
    (hab : a ≤ b) (hb : b ≤ N) (S : Finset ℕ) (hs : S ⊆ Finset.Icc 1 N)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) {ε δ : ℝ} (hδ : 0 ≤ δ)
    (near : (1-δ)*(maxCard k N : ℝ) ≤ S.card)
    (profile : ∀ y ≤ N, |(maxCard k y : ℝ)/maxCard k N-(y:ℝ)/N| ≤ ε) :
    |((S.filter (fun x => a < x ∧ x ≤ b)).card : ℝ)/maxCard k N-
      ((b-a:ℕ):ℝ)/N| ≤ 2*ε+δ := by
  have rp := max_card_pos hk hN
  have ep : 0 ≤ ε := (abs_nonneg _).trans (profile 0 (Nat.zero_le _))
  have split : (S.filter (· ≤ a)).card+(S.filter (fun x => a < x ∧ x ≤ b)).card =
      (S.filter (· ≤ b)).card := by
    have lp : (S.filter (· ≤ b)).filter (· ≤ a) = S.filter (· ≤ a) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · exact fun ⟨⟨hx,_⟩,ha⟩ => ⟨hx,ha⟩
      · exact fun ⟨hx,ha⟩ => ⟨⟨hx,ha.trans hab⟩,ha⟩
    have hp : (S.filter (· ≤ b)).filter (fun x => ¬ x ≤ a) =
        S.filter (fun x => a < x ∧ x ≤ b) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · exact fun ⟨⟨hx,hb⟩,ha⟩ => ⟨hx,by omega,hb⟩
      · exact fun ⟨hx,ha,hb⟩ => ⟨⟨hx,hb⟩,by omega⟩
    simpa only [lp,hp] using
      (Finset.card_filter_add_card_filter_not (s := S.filter (· ≤ b)) (p := (· ≤ a)))
  have splitR : ((S.filter (· ≤ a)).card : ℝ)+
      ((S.filter (fun x => a < x ∧ x ≤ b)).card : ℝ) = (S.filter (· ≤ b)).card := by
    exact_mod_cast split
  have splitDiv := congrArg (fun t : ℝ => t/maxCard k N) splitR
  rw [add_div] at splitDiv
  have bLow := (abs_le.mp (prefix_discrepancy hk hN hb S hs hf hδ near profile)).1
  have aCap : ((S.filter (· ≤ a)).card : ℝ) ≤ maxCard k a := by
    exact_mod_cast prefix_count_le (by omega : 1<k) S hs hf
  have aHigh := (div_le_div_of_nonneg_right aCap rp.le).trans
    (by linarith [(abs_le.mp (profile a (hab.trans hb))).2] :
      (maxCard k a:ℝ)/maxCard k N ≤ (a:ℝ)/N+ε)
  have iCap : ((S.filter (fun x => a < x ∧ x ≤ b)).card : ℝ) ≤ maxCard k (b-a) := by
    exact_mod_cast interval_count_le (by omega : 1<k) S hf
  have iHigh := (div_le_div_of_nonneg_right iCap rp.le).trans
    (by linarith [(abs_le.mp (profile (b-a) (by omega))).2] :
      (maxCard k (b-a):ℝ)/maxCard k N ≤ ((b-a:ℕ):ℝ)/N+ε)
  rw [Nat.cast_sub hab,sub_div] at iHigh ⊢
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- An endpoint is exceptional if some near-extremizer has a large discrepancy
on some subinterval. -/
def badNearIntervalEndpoint (k N : ℕ) (ε δ : ℝ) : Prop :=
  0 < N ∧ ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧
    (S : Set ℕ).IsAPOfLengthFree k ∧
    (1-δ)*(maxCard k N : ℝ) ≤ S.card ∧
    ∃ a b : ℕ, a ≤ b ∧ b ≤ N ∧
      2*ε+δ < |((S.filter (fun x => a < x ∧ x ≤ b)).card : ℝ)/maxCard k N-
        ((b-a:ℕ):ℝ)/N|

theorem bad_near_interval_implies_bad_profile {k N : ℕ} (hk : 3 ≤ k)
    {ε δ : ℝ} (hδ : 0 ≤ δ) :
    badNearIntervalEndpoint k N ε δ → badEndpoint k N ε := by
  rintro ⟨hN,S,hs,hf,near,a,b,hab,hb,bad⟩
  by_contra good
  have profile : ∀ y ≤ N, |(maxCard k y : ℝ)/maxCard k N-(y:ℝ)/N| ≤ ε := by
    intro y hy
    exact le_of_not_gt (fun h => good ⟨y,hy,h⟩)
  exact (not_lt_of_ge (interval_discrepancy hk hN hab hb S hs hf hδ near profile)) bad

noncomputable def nearIntervalWeight (k N : ℕ) (ε δ : ℝ) : ℝ := by
  classical
  exact if badNearIntervalEndpoint k N ε δ then (N:ℝ)⁻¹ else 0

noncomputable def nearIntervalLogMass (k X : ℕ) (ε δ : ℝ) : ℝ :=
  ∑ N ∈ Finset.range X, nearIntervalWeight k N ε δ

theorem near_interval_mass_le {k X : ℕ} (hk : 3 ≤ k) {ε δ : ℝ} (hδ : 0 ≤ δ) :
    nearIntervalLogMass k X ε δ ≤ logMass k X ε := by
  classical
  apply Finset.sum_le_sum
  intro N _
  unfold nearIntervalWeight badWeight
  split_ifs with h h'
  · exact le_rfl
  · exact False.elim (h' (bad_near_interval_implies_bad_profile hk hδ h))
  · positivity
  · exact le_rfl

/-- Uniformly in k and the allowed loss δ, the logarithmic mass of endpoints
admitting any badly distributed near-extremizer is O(sqrt(log X)). -/
theorem logarithmic_near_extremizer_bound {ε : ℝ} (he : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k → ∀ δ : ℝ, 0 ≤ δ → ∀ X : ℕ, 2 ≤ X →
      nearIntervalLogMass k X ε δ ≤ C*Real.sqrt (Real.log X) := by
  obtain ⟨C,hC,bound⟩ := logarithmic_mass_bound he
  exact ⟨C,hC,fun k hk δ hδ X hX =>
    (near_interval_mass_le hk hδ).trans (bound k hk X hX)⟩

/-- At logarithmic-density-one endpoints, every near-extremizer has the asserted
interval distribution. This statement does not determine maxCard's amplitude. -/
theorem logarithmic_near_extremizer_density_one {k : ℕ} (hk : 3 ≤ k)
    {ε δ : ℝ} (he : 0 < ε) (hδ : 0 ≤ δ) :
    Tendsto (fun X : ℕ => nearIntervalLogMass k X ε δ/Real.log X) atTop (𝓝 0) := by
  have lim := logarithmic_density_one hk he
  apply squeeze_zero' _ _ lim
  · filter_upwards [eventually_ge_atTop 2] with X hX
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro N _
      unfold nearIntervalWeight
      split <;> positivity
    · exact (Real.log_pos (show 1 < (X:ℝ) by exact_mod_cast (show 1 < X by omega))).le
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have pos := Real.log_pos (show 1 < (X:ℝ) by exact_mod_cast (show 1 < X by omega))
    exact div_le_div_of_nonneg_right (near_interval_mass_le hk hδ) pos.le

#print axioms interval_discrepancy
#print axioms logarithmic_near_extremizer_bound
#print axioms logarithmic_near_extremizer_density_one

end Erdos142Equidistribution
