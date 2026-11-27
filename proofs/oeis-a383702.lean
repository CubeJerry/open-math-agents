import OMAStatements.S_oeis_a383702
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

namespace OMA.S_oeis_a383702

open Polynomial

lemma polynomial_identity (n : ℕ) :
    product (n+3) + C (3*(-4*((n:ℤ)+3)+5)) * product (n+2) +
      C (48*((n:ℤ)+3)^2-168*((n:ℤ)+3)+151)*product (n+1) -
      C ((4*((n:ℤ)+3)-9)^3)*product n = X^3*product n := by
  simp only [product, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_one]
  ring

theorem solution : ∀ n : ℕ, a (n+3) + 3*(-4*((n:ℤ)+3)+5)*a (n+2) +
    (48*((n:ℤ)+3)^2 - 168*((n:ℤ)+3) + 151)*a (n+1) -
    (4*((n:ℤ)+3)-9)^3*a n = 0 := by
  intro n
  have h := congrArg (fun p : Polynomial ℤ => p.coeff 2) (polynomial_identity n)
  change _ = (X^3 * product n).coeff 2 at h
  simp only [coeff_sub,coeff_add,coeff_C_mul,coeff_X_pow_mul',show ¬3≤2 by decide,if_false] at h
  exact h

end OMA.S_oeis_a383702

theorem OMA.solution : type_of% @OMA.S_oeis_a383702.main :=
  OMA.S_oeis_a383702.solution
