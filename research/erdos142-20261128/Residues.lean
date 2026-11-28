import Equidistribution

namespace Erdos142Equidistribution

open Set.IsAPOfLengthFree ProgressionParity
open scoped BigOperators

theorem residue_count_le {k N q r : ℕ} (hk : 1 < k) (hq : 0 < q)
    (S : Finset ℕ) (hs : S ⊆ Finset.Icc 1 N)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) :
    (S.filter (fun x => x%q=r)).card ≤ maxCard k (N/q+1) := by
  let H := S.filter (fun x => x%q=r)
  let T := H.image (fun x => x/q+1)
  have tc : T.card = H.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy eq
    have xr := (Finset.mem_filter.mp hx).2
    have yr := (Finset.mem_filter.mp hy).2
    change x/q+1 = y/q+1 at eq
    have dx := Nat.mod_add_div x q
    have dy := Nat.mod_add_div y q
    have same : x/q=y/q := Nat.add_right_cancel eq
    rw [same,xr] at dx
    rw [yr] at dy
    exact dx.symm.trans dy
  have hc : T.card ≤ maxCard k (N/q+1) := by
    apply bound_witness hk
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      have high := (Finset.mem_Icc.mp (hs (Finset.mem_filter.mp hx).1)).2
      exact Finset.mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le _),
        Nat.add_le_add_right (Nat.div_le_div_right high) 1⟩
    · intro a d hd run
      have terms := (run_iff_forall _ _ _ _).mp run
      have first := terms 0 (by omega)
      obtain ⟨x0,_,e0⟩ := Finset.mem_image.mp first
      have ap : 1 ≤ a := by
        have pos : 1 ≤ x0/q+1 := Nat.succ_le_succ (Nat.zero_le _)
        change x0/q+1=a+0*d at e0
        simp only [Nat.zero_mul,Nat.add_zero] at e0
        exact e0 ▸ pos
      apply (upstream_iff_free (S : Set ℕ) hk).mp hf (q*(a-1)+r) (q*d) (Nat.mul_pos hq hd)
      apply (run_iff_forall _ _ _ _).mpr
      intro i hi
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp (terms i hi)
      obtain ⟨sx,rem⟩ := Finset.mem_filter.mp hx
      change x/q+1 = a+i*d at eq
      have decode : x = q*(a+i*d-1)+r := by
        have dx := Nat.mod_add_div x q
        have div : x/q=a+i*d-1 := by omega
        rw [div,rem] at dx
        omega
      have move : a+i*d-1=(a-1)+i*d := by omega
      rw [move,Nat.mul_add] at decode
      rwa [show q*(a-1)+r+i*(q*d)=x by nlinarith [decode]]
  rwa [tc] at hc

/-- A bounded residue modulus is controlled by the same extremal profile. The
term q/N accounts for the rounding of residue-class lengths. -/
theorem residue_discrepancy {k N q r : ℕ} (hk : 3 ≤ k) (hN : 0 < N)
    (hq : 2 ≤ q) (hr : r < q) (S : Finset ℕ) (hs : S ⊆ Finset.Icc 1 N)
    (hf : (S : Set ℕ).IsAPOfLengthFree k) {ε δ : ℝ} (hδ : 0 ≤ δ)
    (near : (1-δ)*(maxCard k N : ℝ) ≤ S.card)
    (profile : ∀ y ≤ N, |(maxCard k y : ℝ)/maxCard k N-(y:ℝ)/N| ≤ ε) :
    |((S.filter (fun x => x%q=r)).card : ℝ)/maxCard k N-1/(q:ℝ)| ≤
      q*(ε+1/(N:ℝ))+δ := by
  have qp : 0 < (q:ℝ) := by exact_mod_cast (show 0<q by omega)
  have qone : 1 ≤ (q:ℝ) := by exact_mod_cast (show 1≤q by omega)
  have np : 0 < (N:ℝ) := by exact_mod_cast hN
  have rp := max_card_pos hk hN
  have ep : 0 ≤ ε := (abs_nonneg _).trans (profile 0 (Nat.zero_le _))
  let η : ℝ := ε+1/(N:ℝ)
  have ηpos : 0 ≤ η := by dsimp [η];positivity
  have short : N/q+1 ≤ N := by have := Nat.div_lt_self hN hq;omega
  have mesh : ((N/q+1:ℕ):ℝ)/(N:ℝ) ≤ 1/(q:ℝ)+1/(N:ℝ) := by
    have le := div_le_div_of_nonneg_right (Nat.cast_div_le (m := N) (n := q) (α := ℝ)) np.le
    have id : ((N:ℝ)/(q:ℝ))/(N:ℝ)=1/(q:ℝ) := by field_simp
    rw [id] at le
    push_cast
    rw [add_div]
    linarith
  let v : ℕ → ℝ := fun a => ((S.filter (fun x => x%q=a)).card : ℝ)/maxCard k N
  have cap (a : ℕ) : v a ≤ 1/(q:ℝ)+η := by
    have raw : ((S.filter (fun x => x%q=a)).card : ℝ) ≤ maxCard k (N/q+1) := by
      exact_mod_cast residue_count_le (by omega : 1<k) (by omega : 0<q) S hs hf
    have bound := div_le_div_of_nonneg_right raw rp.le
    have prof := (abs_le.mp (profile (N/q+1) short)).2
    dsimp only [v,η]
    linarith
  have totalNat : S.card = ∑ a ∈ Finset.range q, (S.filter (fun x => x%q=a)).card := by
    exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_range.mpr (Nat.mod_lt x (by omega)))
  have total : ∑ a ∈ Finset.range q, v a = (S.card : ℝ)/maxCard k N := by
    dsimp only [v]
    rw [← Finset.sum_div]
    congr 1
    exact_mod_cast totalNat.symm
  have rest : ∑ a ∈ (Finset.range q).erase r, v a ≤ ((q:ℝ)-1)*(1/(q:ℝ)+η) := by
    calc
      _ ≤ ∑ _a ∈ (Finset.range q).erase r, (1/(q:ℝ)+η) :=
        Finset.sum_le_sum (fun a _ => cap a)
      _ = _ := by
        rw [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_range.mpr hr),Finset.card_range]
        simp only [nsmul_eq_mul]
        rw [Nat.cast_sub (by omega : 1≤q),Nat.cast_one]
  have split := Finset.sum_erase_add (s := Finset.range q) v (Finset.mem_range.mpr hr)
  rw [total] at split
  have low : 1-δ ≤ (S.card:ℝ)/maxCard k N := (le_div_iff₀ rp).mpr near
  have high := cap r
  have cancel : (q:ℝ)*(1/(q:ℝ))=1 := by field_simp
  change |v r-1/(q:ℝ)| ≤ (q:ℝ)*η+δ
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

#print axioms residue_discrepancy

end Erdos142Equidistribution
