import FormalConjecturesForMathlib.Combinatorics.AP.Basic
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Lean.Elab.Tactic.Omega

/-!
Bridge from Mathlib's extremal function on `range N` to the exact extremal
function used in FormalConjectures/ErdosProblems/142.lean. That file defines
`Erdos142.r` as an abbreviation for `Set.IsAPOfLengthFree.maxCard`, so the final
theorem below has exactly the required target at `k = 3`, without importing any
of the open problem's placeholder declarations.

Prepared separately from the geometry, with only the defining upstream AP
module and Mathlib's Roth-number definitions imported.
-/

namespace Erdos142Bridge

theorem threeAPFree_isAPOfLengthFree {S : Set ℕ} (h : ThreeAPFree S) :
    S.IsAPOfLengthFree 3 := by
  intro T hsub hAP
  obtain ⟨a, d, hcard, heq⟩ := hAP
  have h0 : a ∈ T := by
    rw [heq]
    exact ⟨0, by decide, by simp⟩
  have h1 : a + d ∈ T := by
    rw [heq]
    exact ⟨1, by decide, by simp⟩
  have h2 : a + 2 * d ∈ T := by
    rw [heq]
    exact ⟨2, by decide, by simp [two_mul]⟩
  have hab := h (hsub h0) (hsub h1) (hsub h2) (by omega)
  have hd : d = 0 := by omega
  have hsingleton : T = {a} := by
    ext x
    rw [heq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      simp [hd]
    · intro hx
      have hx' : x = a := hx
      exact ⟨0, by decide, by simp [hx']⟩
  rw [hsingleton] at hcard
  simpa using hcard.ge

theorem card_le_maxCard_three {N : ℕ} (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) (hfree : ThreeAPFree (A : Set ℕ)) :
    A.card ≤ Set.IsAPOfLengthFree.maxCard 3 N := by
  classical
  have hb : BddAbove
      {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
        (_ : (S : Set ℕ).IsAPOfLengthFree (3 : ℕ))} := by
    refine ⟨(Finset.Icc 1 N).card, ?_⟩
    rintro n ⟨S, hS, _, rfl⟩
    exact Finset.card_le_card hS
  exact le_csSup hb ⟨A, hA, threeAPFree_isAPOfLengthFree hfree, rfl⟩

theorem rothNumberNat_eq_interval (N : ℕ) :
    rothNumberNat N = addRothNumber (Finset.Icc 1 N) := by
  have he : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [he, addRothNumber_Ico]
  congr 1

/-- A Mathlib Roth-number lower bound is a lower bound for `Erdos142.r 3 N`. -/
theorem rothNumberNat_le_maxCard_three (N : ℕ) :
    rothNumberNat N ≤ Set.IsAPOfLengthFree.maxCard 3 N := by
  rw [rothNumberNat_eq_interval]
  obtain ⟨A, hA, hcard, hfree⟩ := addRothNumber_spec (Finset.Icc 1 N)
  rw [← hcard]
  exact card_le_maxCard_three A hA hfree

#print axioms rothNumberNat_le_maxCard_three

end Erdos142Bridge
