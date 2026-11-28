import SixWidthsRoth
import RothBridge

/-!
The concrete 192-layer certificate, transferred to the exact extremal function
used by Erdős problem 142. This is a lower bound, not a ratio-one asymptotic.

The target is written as `Set.IsAPOfLengthFree.maxCard 3 N`, which is
definitionally `Erdos142.r 3 N` in the upstream problem file. The problem file
itself is not imported, so none of its open placeholders enters this proof.
-/

namespace Erdos142LowerBound
noncomputable section

/-- Every coefficient above `2 sqrt(log(10/3))` is a valid eventual
lower-bound coefficient for the original `[1,N]` extremal function. -/
theorem r_three_eventual_of_constant (C : ℝ)
    (hC : 2 * Real.sqrt (Real.log (10 / 3)) < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) ≤
        (Set.IsAPOfLengthFree.maxCard 3 N : ℝ) := by
  obtain ⟨N₀, hN₀⟩ :=
    Erdos142BlockCertificate.SixWidths192.roth_eventual_three_tenths C hC
  refine ⟨N₀, ?_⟩
  intro N hN
  exact (hN₀ N hN).trans (by
    exact_mod_cast Erdos142Bridge.rothNumberNat_le_maxCard_three N)

theorem r_three_eventual_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * Real.exp (-(2 * Real.sqrt (Real.log (10 / 3)) + ε) *
        Real.sqrt (Real.log (N : ℝ))) ≤
          (Set.IsAPOfLengthFree.maxCard 3 N : ℝ) :=
  r_three_eventual_of_constant _ (by linarith)

theorem leading_constant_lt_ehps :
    2 * Real.sqrt (Real.log (10 / 3)) <
      2 * Real.sqrt (Real.log (24 / 7)) := by
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 10 / 3)
    (by norm_num : (10 / 3 : ℝ) < 24 / 7)
  have ha := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 10 / 3)
  have hs := Real.sqrt_lt_sqrt ha h
  linarith

/-- A strict improvement on the EHPS coefficient, stated directly for
the extremal function in the upstream Erdős 142 definition. -/
theorem r_three_leading_constant_improvement :
    ∃ C : ℝ, 0 < C ∧ C < 2 * Real.sqrt (Real.log (24 / 7)) ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) ≤
          (Set.IsAPOfLengthFree.maxCard 3 N : ℝ) := by
  let lo := 2 * Real.sqrt (Real.log (10 / 3))
  let hi := 2 * Real.sqrt (Real.log (24 / 7))
  have hlt : lo < hi := leading_constant_lt_ehps
  have hlo : 0 ≤ lo := by dsimp [lo]; positivity
  let C := (lo + hi) / 2
  have hC : lo < C := by dsimp [C]; linarith
  have hChi : C < hi := by dsimp [C]; linarith
  exact ⟨C, lt_of_le_of_lt hlo hC, hChi, r_three_eventual_of_constant C hC⟩

#print axioms r_three_eventual_of_constant
#print axioms r_three_eventual_epsilon
#print axioms r_three_leading_constant_improvement

end
end Erdos142LowerBound
