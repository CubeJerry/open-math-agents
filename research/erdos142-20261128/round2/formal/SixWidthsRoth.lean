import CellFamily192

/-!
The concrete density 3/10 certificate implies the following ordinary lower
bound for the actual natural-number Roth extremal function. This is a partial
result related to Erdős 142, not the ratio-one asymptotic problem itself.
-/

namespace Erdos142BlockCertificate.SixWidths192

open Real

theorem roth_eventual_three_tenths (C : ℝ)
    (hC : 2*sqrt (log (10/3))<C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N →
      (N:ℝ)*exp (-C*sqrt (log (N:ℝ)))≤(rothNumberNat N:ℝ) := by
  apply roth_eventual_of_constant (3/10) 6000000000003 60000000000
    density_three_tenths (by norm_num) (by norm_num) C
  norm_num at hC ⊢
  exact hC

#print axioms roth_eventual_three_tenths

end Erdos142BlockCertificate.SixWidths192
