import OMAStatements.S_oeis_a365383

namespace OMA.S_oeis_a365383

lemma append_parts {n k : ℕ} (p : Nat.Partition n) (h : Represents p k) :
    Represents p (k + n) := by
  obtain ⟨xs, hx, he⟩ := h
  refine ⟨xs + p.parts, ?_, by simp [he, p.parts_sum]⟩
  intro x hx'
  exact (Multiset.mem_add.mp hx').elim (hx x) id

lemma row_step (n k : ℕ) : row n k ≤ row n (k+n) := by
  classical
  apply Finset.card_le_card
  intro p hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, append_parts p (Finset.mem_filter.mp hp).2⟩

lemma bounded_stable {f : ℕ → ℕ} {B : ℕ} (h : Monotone f) (hb : ∀ j, f j ≤ B) :
    ∃ J, ∀ j ≥ J, f j = f J := by
  classical
  let P := fun v => ∃ j, f j = v
  have ht : P (Nat.findGreatest P B) := Nat.findGreatest_spec (hb 0) ⟨0,rfl⟩
  obtain ⟨J, hJ⟩ := ht
  refine ⟨J, fun j hj => le_antisymm ?_ (h hj)⟩
  rw [hJ]
  exact Nat.le_findGreatest (hb j) ⟨j, rfl⟩

lemma eventually_periodic : ∀ n : ℕ, ∃ K : ℕ, ∀ k ≥ K, row n (k + n) = row n k := by
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · exact ⟨0, fun _ _ => rfl⟩
  classical
  have stable (r : Fin n) :
      ∃ J, ∀ j ≥ J, row n (r.val+j*n) = row n (r.val+J*n) := by
    apply bounded_stable (B := Fintype.card (Nat.Partition n))
    · apply monotone_nat_of_le_succ
      intro j
      simpa [Nat.succ_mul, Nat.add_assoc] using row_step n (r.val+j*n)
    · intro j
      exact Finset.card_le_univ _
  choose J hJ using stable
  let M := Finset.univ.sup J
  refine ⟨M*n, ?_⟩
  intro k hk
  let r : Fin n := ⟨k%n, Nat.mod_lt _ hn⟩
  have hM : J r ≤ M := Finset.le_sup (Finset.mem_univ r)
  have hq : M ≤ k/n := (Nat.le_div_iff_mul_le hn).2 hk
  have hh := (hJ r (k/n+1) (by omega)).trans (hJ r (k/n) (by omega)).symm
  have he : r.val + k/n*n = k := by
    simpa [r, Nat.mul_comm] using Nat.mod_add_div k n
  rw [Nat.succ_mul, ← Nat.add_assoc, he] at hh
  exact hh

lemma represents_multiple {n : ℕ} (p : Nat.Partition n) (j : ℕ) : Represents p (j*n) := by
  induction j with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ j ih => simpa only [Nat.succ_mul] using append_parts p ih

lemma full_iff {n k : ℕ} (hn : 0 < n) : row n k = Fintype.card (Nat.Partition n) ↔ n ∣ k := by
  classical
  unfold row
  rw [← Finset.card_univ, Finset.card_filter_eq_iff]
  constructor
  · intro h
    obtain ⟨xs,hxs,rfl⟩ := h (Nat.Partition.indiscrete n) (Finset.mem_univ _)
    have hall : ∀ x ∈ xs, n ∣ x := by
      intro x hx
      have hm := hxs x hx
      rw [Nat.Partition.indiscrete_parts hn.ne', Multiset.mem_singleton] at hm
      exact hm ▸ dvd_rfl
    clear hxs h
    induction xs using Multiset.induction_on with
    | empty => simp
    | cons x s ih =>
      rw [Multiset.sum_cons]
      exact dvd_add (hall _ (Multiset.mem_cons_self ..))
        (ih (fun y hy => hall y (Multiset.mem_cons_of_mem hy)))
  · rintro ⟨j,rfl⟩ p _
    simpa [Nat.mul_comm] using represents_multiple p j

lemma divides_period {n t : ℕ} (hn : 0 < n)
    (ht : ∃ K, ∀ k ≥ K, row n (k+t) = row n k) : n ∣ t := by
  obtain ⟨K,hK⟩ := ht
  have hk : K ≤ K*n := Nat.le_mul_of_pos_right K hn
  have hd : n ∣ K*n := dvd_mul_left _ _
  have hf := (full_iff hn).2 hd
  have hf' := (full_iff hn).1 ((hK _ hk).trans hf)
  exact (Nat.dvd_add_right hd).mp hf'

theorem solution : (∀ n : ℕ, ∃ K : ℕ, ∀ k ≥ K, row n (k+n) = row n k) ∧
    (∀ n t : ℕ, 0 < n → (∃ K : ℕ, ∀ k ≥ K, row n (k+t) = row n k) → n ∣ t) :=
  ⟨eventually_periodic, fun _ _ hn ht => divides_period hn ht⟩

end OMA.S_oeis_a365383

theorem OMA.solution : type_of% @OMA.S_oeis_a365383.main :=
  OMA.S_oeis_a365383.solution
