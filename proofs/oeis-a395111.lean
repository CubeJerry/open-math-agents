import OMAStatements.S_oeis_a395111
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.IntervalCases

namespace OMA.S_oeis_a395111

open Filter Topology

lemma square_mono (n : ℕ) : Monotone (fun L => squareWays L n) := by
  apply monotone_nat_of_le_succ
  intro L
  exact Nat.le_add_right _ _

lemma add_prime {n p : ℕ} (hp : p.Prime) : squareWays (p-1) n ≤ squareWays p (n+p) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  subst p
  simp [squareWays, hp.squarefree]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
lemma witness : A 44 = 53 := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
lemma small_values : ∀ n : Fin 33, B n ≠ 53 := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
lemma base_range : ∀ j : Fin 38, 54 ≤ squareWays 18 (33+j.val) := by decide +kernel

lemma many (n : ℕ) (hn : 33 ≤ n) : 54 ≤ squareWays (max 18 (n-33)) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n ≤ 70
    · let j : Fin 38 := ⟨n-33, by omega⟩
      have h := base_range j
      change 54 ≤ squareWays 18 (33+(n-33)) at h
      rw [show 33+(n-33)=n by omega] at h
      exact h.trans (square_mono n (le_max_left ..))
    · obtain ⟨p,hp,hl,hu⟩ := Nat.exists_prime_lt_and_le_two_mul ((n-33)/2) (by omega)
      have h := ih (n-p) (by omega) (by omega)
      have hsmall : max 18 (n-p-33) ≤ p-1 := by omega
      have hlarge : p ≤ max 18 (n-33) := by omega
      have hh := (h.trans (square_mono _ hsmall)).trans (add_prime hp)
      rw [show n-p+p=n by omega] at hh
      exact hh.trans (square_mono _ hlarge)

theorem missing (n : ℕ) : B n ≠ 53 := by
  by_cases hn : n < 33
  · exact small_values ⟨n,hn⟩
  · have hh := (many n (by omega)).trans (square_mono n (show max 18 (n-33) ≤ n by omega))
    change 54 ≤ squareWays n n at hh
    exact Nat.ne_of_gt hh

theorem disproof : ¬ (Set.range A = Set.range B ∧
    Tendsto (fun N : ℕ => ((((Finset.range N).filter (fun n => A n = 1)).card : ℕ) : ℝ) / N)
      atTop (𝓝 0)) := by
  rintro ⟨he,_⟩
  have h : 53 ∈ Set.range A := ⟨44,witness⟩
  rw [he] at h
  obtain ⟨n,h⟩ := h
  exact missing n h

end OMA.S_oeis_a395111

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a395111.main) :=
  OMA.S_oeis_a395111.disproof
