import OMAStatements.S_oeis_a386834

-- Credit: @CubeJerry (the owner of the agent is credited as the solver)

/-!
A creative-telescoping proof of R. J. Mathar's recurrence conjecture for A386834.
Reflecting the binomial summand gives a rational hypergeometric term. An exact
certificate establishes an order-two recurrence; two consecutive instances
then imply the original order-three recurrence. All algebra and finite sums
are checked by the Lean kernel.
-/

namespace OMA.T386834

def p0 (n : ℚ) : ℚ := 3*n*(3*n-2)*(3*n-1)*(77*n^3-347*n^2+516*n-252)
def p1 (n : ℚ) : ℚ := -(37345*n^6-227431*n^5+539727*n^4-630029*n^3+373808*n^2-103260*n+9360)
def p2 (n : ℚ) : ℚ := -16*(2*n-3)*(4*n-5)*(4*n-3)*(77*n^3-116*n^2+53*n-6)

def back (n k : ℚ) : ℚ :=
  (n-k)*(3*n-1)*(3*n-2)*(3*n-3)*(3*n+k)*(3*n+k+1) /
  ((4*n+1)*(4*n)*(4*n-1)*(4*n-2)*(3*n+k-3)*(3*n+k-2))

def right (n k : ℚ) : ℚ := (n-k)*(3*n+k)/((k+1)*(3*n+k+2))

def certPoly (n k : ℚ) : ℚ :=
  (((((((3*(n - 2)*(3*n - 5)*(3*n - 4)*(77*n^3 - 116*n^2 + 53*n - 6))) * k + (2*(4697*n^7 - 33949*n^6 + 96449*n^5 - 138433*n^4 + 107702*n^3 - 45262*n^2 + 9396*n - 720))) * k + (-139755*n^8 + 1150171*n^7 - 4077234*n^6 + 8071978*n^5 - 9647979*n^4 + 7016095*n^3 - 2967600*n^2 + 645492*n - 51120)) * k + (-2*(699930*n^9 - 6304146*n^8 + 24603014*n^7 - 54483967*n^6 + 75197309*n^5 - 66715033*n^4 + 37707431*n^3 - 12898498*n^2 + 2362032*n - 167040))) * k + (-5041575*n^10 + 49468239*n^9 - 212135931*n^8 + 522739625*n^7 - 818061600*n^6 + 846837668*n^5 - 583914678*n^4 + 262189412*n^3 - 72206424*n^2 + 10771536*n - 645120)) * k + (-6*(1386693*n^11 - 14730057*n^10 + 68812677*n^9 - 186086894*n^8 + 322665067*n^7 - 375308863*n^6 + 297398227*n^5 - 159383738*n^4 + 55902952*n^3 - 11950144*n^2 + 1354944*n - 60480))) * k + (-9*n*(588357*n^11 - 6727653*n^10 + 33973140*n^9 - 99641810*n^8 + 187950845*n^7 - 238710065*n^6 + 207896578*n^5 - 124097064*n^4 + 49817832*n^3 - 12833072*n^2 + 1903488*n - 120960))

def R (n k : ℚ) : ℚ :=
  3*k*(3*n-2)*(3*n-1)*(k+3*n+1)*certPoly n k /
  (8*n*(2*n-1)*(4*n-1)*(4*n+1)*
    (k+3*n-6)*(k+3*n-5)*(k+3*n-4)*(k+3*n-3)*(k+3*n-2)*(k+3*n-1))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma poly_cert (n k : ℚ) :
    (n-k)*(k+3*n-6)*certPoly n (k+1)-k*(k+3*n+1)*certPoly n k =
    n*(77*n^3-347*n^2+516*n-252)*(8*n*(2*n-1)*(4*n-1)*(4*n+1))*
      ((k+3*n-1)*(k+3*n-2)*(k+3*n-3)*(k+3*n-4)*(k+3*n-5)*(k+3*n-6)) +
    (n-1)*p1 n*(n-k)*(k+3*n)*(k+3*n+1)*
      ((k+3*n-1)*(k+3*n-4)*(k+3*n-5)*(k+3*n-6)) -
    6*(n-2)*(3*n-4)*(3*n-5)*(77*n^3-116*n^2+53*n-6)*(n-k)*(n-k-1)*
      (k+3*n)*(k+3*n+1)*((k+3*n-1)*(k+3*n-2)*(k+3*n-3)*(k+3*n-4)) := by
  unfold certPoly p1
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma left_cert (n k : ℚ) (hn : 3 ≤ n) (hk : 0 ≤ k) :
    right n k * R n (k+1)-R n k =
    3*(3*n-2)*(3*n-1)*
      ((n-k)*(k+3*n-6)*certPoly n (k+1)-k*(k+3*n+1)*certPoly n k) /
    (8*n*(2*n-1)*(4*n-1)*(4*n+1)*
     (k+3*n-6)*(k+3*n-5)*(k+3*n-4)*(k+3*n-3)*(k+3*n-2)*(k+3*n-1)) := by
  have h0 : n > 0 := by linarith
  have h1 : k+1 > 0 := by linarith
  have h2 : k+3*n+2 > 0 := by linarith
  have h3 : 2*n-1 > 0 := by linarith
  have h4 : 4*n-1 > 0 := by linarith
  have h5 : 4*n+1 > 0 := by linarith
  have h6 : k+3*n-0 > 0 := by linarith
  have h7 : k+3*n-1 > 0 := by linarith
  have h8 : k+3*n-2 > 0 := by linarith
  have h9 : k+3*n-3 > 0 := by linarith
  have h10 : k+3*n-4 > 0 := by linarith
  have h11 : k+3*n-5 > 0 := by linarith
  have h12 : k+3*n-6 > 0 := by linarith
  unfold right R
  rw [show 3*n+k = k+3*n by ring]
  rw [show k+1+3*n+1 = k+3*n+2 by ring]
  rw [show k+1+3*n-1 = k+3*n-0 by ring]
  rw [show k+1+3*n-2 = k+3*n-1 by ring]
  rw [show k+1+3*n-3 = k+3*n-2 by ring]
  rw [show k+1+3*n-4 = k+3*n-3 by ring]
  rw [show k+1+3*n-5 = k+3*n-4 by ring]
  rw [show k+1+3*n-6 = k+3*n-5 by ring]
  field_simp (disch := linarith)
  ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
lemma certQ (n k : ℚ) (hn : 3 ≤ n) (hk : 0 ≤ k) :
    right n k * R n (k+1) - R n k =
      p0 n + p1 n * back n k + p2 n * back n k * back (n-1) k := by
  rw [left_cert n k hn hk, poly_cert]
  have h0 : n > 0 := by linarith
  have h1 : k+1 > 0 := by linarith
  have h2 : 3*n+k+2 > 0 := by linarith
  have h3 : 4*n+1 > 0 := by linarith
  have h4 : 4*n > 0 := by linarith
  have h5 : 4*n-1 > 0 := by linarith
  have h6 : 4*n-2 > 0 := by linarith
  have h7 : 3*n+k-3 > 0 := by linarith
  have h8 : 3*n+k-2 > 0 := by linarith
  have h9 : 2*n-1 > 0 := by linarith
  have h10 : 4*(n-1)+1 > 0 := by linarith
  have h11 : 4*(n-1) > 0 := by linarith
  have h12 : 4*(n-1)-1 > 0 := by linarith
  have h13 : 4*(n-1)-2 > 0 := by linarith
  have h14 : 3*(n-1)+k-3 > 0 := by linarith
  have h15 : 3*(n-1)+k-2 > 0 := by linarith
  have h16 : k+3*n-1 > 0 := by linarith
  have h17 : k+3*n-2 > 0 := by linarith
  have h18 : k+3*n-3 > 0 := by linarith
  have h19 : k+3*n-4 > 0 := by linarith
  have h20 : k+3*n-5 > 0 := by linarith
  have h21 : k+3*n-6 > 0 := by linarith
  unfold p0 p1 p2 back
  field_simp (disch := linarith)
  ring

lemma cert (n k : ℕ) (hn : 3 ≤ n) :
    right n k * R n ((k:ℚ)+1) - R n k =
      p0 n + p1 n * back n k + p2 n * back n k * back ((n:ℚ)-1) k := by
  exact certQ n k (by exact_mod_cast hn) (by positivity)

end OMA.T386834

namespace OMA.T386834

noncomputable def P (n : ℕ) : ℚ :=
  ((4 * n + 1).factorial : ℚ) / ((n.factorial : ℚ) * ((3 * n - 1).factorial : ℚ))

noncomputable def F (n k : ℕ) : ℚ :=
  (n.choose k : ℚ) * P n / ((3 * (n : ℚ) + k) * (3 * (n : ℚ) + k + 1))

lemma choose_rat (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℚ) = (n.factorial : ℚ) /
      ((k.factorial : ℚ) * ((n - k).factorial : ℚ)) := by
  apply (eq_div_iff (by positivity)).2
  have h := Nat.choose_mul_factorial_mul_factorial hk
  exact_mod_cast (by simpa [mul_assoc] using h)

lemma factorial_two_up (m : ℕ) (hm : 1 ≤ m) :
    ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * m * ((m - 1).factorial : ℚ) := by
  have h : (m.factorial : ℚ) = (m : ℚ) * ((m - 1).factorial : ℚ) := by
    conv_lhs => rw [show m = m - 1 + 1 by omega]
    rw [Nat.factorial_succ]
    push_cast
    have hcast : ((m - 1 : ℕ) : ℚ) + 1 = m := by exact_mod_cast (Nat.sub_add_cancel hm)
    rw [hcast]
  rw [Nat.factorial_succ]
  push_cast
  rw [h]
  ring

lemma reflected_term (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    ((4 * n + 1).choose (n - k) : ℚ) * ((3 * n + k - 1).choose k : ℚ) = F n k := by
  rw [F, P, choose_rat (4 * n + 1) (n - k) (by omega),
    choose_rat (3 * n + k - 1) k (by omega), choose_rat n k hk]
  rw [show 4 * n + 1 - (n - k) = 3 * n + k + 1 by omega,
    show 3 * n + k - 1 - k = 3 * n - 1 by omega]
  rw [factorial_two_up (3 * n + k) (by omega)]
  push_cast
  have h0 : (3 * (n : ℚ) + k) ≠ 0 := by positivity
  have h1 : (3 * (n : ℚ) + k + 1) ≠ 0 := by positivity
  field_simp
  <;> ring


lemma F_zero_of_lt (n k : ℕ) (h : n < k) : F n k = 0 := by
  simp [F, Nat.choose_eq_zero_of_lt h]

lemma rightF (n k : ℕ) (hn : 1 ≤ n) :
    F n (k+1) = F n k * right n k := by
  by_cases hk : k ≤ n
  · have hc : (n.choose (k+1) : ℚ) =
        (n.choose k : ℚ) * ((n : ℚ)-k) / ((k : ℚ)+1) := by
      apply (eq_div_iff (by positivity)).2
      have h := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_succ_right_eq n k)
      push_cast [Nat.cast_sub hk] at h
      exact h
    unfold F right
    rw [hc]
    push_cast
    have h0 : 3 * (n : ℚ) + k ≠ 0 := by positivity
    have h1 : 3 * (n : ℚ) + k + 1 ≠ 0 := by positivity
    have h2 : 3 * (n : ℚ) + k + 2 ≠ 0 := by positivity
    have h3 : (k : ℚ)+1 ≠ 0 := by positivity
    field_simp
    <;> ring
  · rw [F_zero_of_lt n (k+1) (by omega), F_zero_of_lt n k (by omega)]
    simp

lemma P_succ_ratio (n : ℕ) (hn : 1 ≤ n) :
    P n = P (n+1) * (((n : ℚ)+1)*(3*n)*(3*n+1)*(3*n+2)) /
      ((4*n+2)*(4*n+3)*(4*n+4)*(4*n+5)) := by
  have h4 : ((4*(n+1)+1).factorial : ℚ) =
      (4*(n : ℚ)+2)*(4*n+3)*(4*n+4)*(4*n+5)*((4*n+1).factorial : ℚ) := by
    rw [show 4*(n+1)+1 = 4*n+1+1+1+1+1 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have h3 : ((3*(n+1)-1).factorial : ℚ) =
      (3*(n : ℚ))*(3*n+1)*(3*n+2)*((3*n-1).factorial : ℚ) := by
    rw [show 3*(n+1)-1 = 3*n-1+1+1+1 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast [Nat.cast_sub (show 1 ≤ 3*n by omega)]
    ring
  unfold P
  rw [h4, h3, Nat.factorial_succ n]
  push_cast
  have h0 : (3*(n:ℚ)) ≠ 0 := by positivity
  have h1 : (3*(n:ℚ)+1) ≠ 0 := by positivity
  have h2 : (3*(n:ℚ)+2) ≠ 0 := by positivity
  have h5 : (4*(n:ℚ)+2) ≠ 0 := by positivity
  have h6 : (4*(n:ℚ)+3) ≠ 0 := by positivity
  have h7 : (4*(n:ℚ)+4) ≠ 0 := by positivity
  have h8 : (4*(n:ℚ)+5) ≠ 0 := by positivity
  field_simp
  <;> ring

lemma backF (n k : ℕ) (hn : 1 ≤ n) :
    F n k = F (n+1) k * back ((n : ℚ)+1) k := by
  by_cases hk : k ≤ n+1
  · have hc : (n.choose k : ℚ) =
        ((n+1).choose k : ℚ) * (((n:ℚ)+1)-k) / ((n:ℚ)+1) := by
      apply (eq_div_iff (by positivity)).2
      have h := congrArg (fun t : ℕ => (t : ℚ)) (Nat.choose_mul_succ_eq n k)
      push_cast [Nat.cast_sub hk] at h
      exact h
    unfold F back
    rw [hc, P_succ_ratio n hn]
    push_cast
    have h0 : (n:ℚ)+1 ≠ 0 := by positivity
    have h1 : 3*(n:ℚ)+k ≠ 0 := by positivity
    have h2 : 3*(n:ℚ)+k+1 ≠ 0 := by positivity
    have h3 : 3*((n:ℚ)+1)+k ≠ 0 := by positivity
    have h4 : 3*((n:ℚ)+1)+k+1 ≠ 0 := by positivity
    have h5 : 4*(n:ℚ)+2 ≠ 0 := by positivity
    have h6 : 4*(n:ℚ)+3 ≠ 0 := by positivity
    have h7 : 4*(n:ℚ)+4 ≠ 0 := by positivity
    have h8 : 4*(n:ℚ)+5 ≠ 0 := by positivity
    have h9 : 4*((n:ℚ)+1)+1 ≠ 0 := by positivity
    have h10 : 4*((n:ℚ)+1) ≠ 0 := by positivity
    have h11 : 4*((n:ℚ)+1)-1 ≠ 0 := by linarith
    have h12 : 4*((n:ℚ)+1)-2 ≠ 0 := by linarith
    have h13 : 3*((n:ℚ)+1)+k-3 ≠ 0 := by
      have hn' : (1:ℚ) ≤ n := by exact_mod_cast hn
      have hk' : (0:ℚ) ≤ k := by positivity
      linarith
    have h14 : 3*((n:ℚ)+1)+k-2 ≠ 0 := by
      have hn' : (1:ℚ) ≤ n := by exact_mod_cast hn
      have hk' : (0:ℚ) ≤ k := by positivity
      linarith
    have hnq : (1:ℚ) ≤ n := by exact_mod_cast hn
    have hkq : (0:ℚ) ≤ k := by positivity
    field_simp (disch := first | positivity | linarith)
    <;> ring
  · rw [F_zero_of_lt n k (by omega), F_zero_of_lt (n+1) k (by omega)]
    simp

lemma reflected_sum (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n+1), ((4*n+1).choose k : ℚ) *
      ((4*n-k-1).choose (n-k) : ℚ)) = ∑ k ∈ Finset.range (n+1), F n k := by
  rw [← Finset.sum_range_reflect (fun k =>
    ((4*n+1).choose k : ℚ) * ((4*n-k-1).choose (n-k) : ℚ)) (n+1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
  simp only [Nat.add_sub_cancel_right]
  rw [show n - (n-k) = k by omega, show 4*n-(n-k)-1 = 3*n+k-1 by omega]
  exact reflected_term n k hn hk'

lemma reflected_sum_int (n : ℕ) (hn : 1 ≤ n) :
    ((∑ k ∈ Finset.range (n+1), ((4*n+1).choose k : ℤ) *
      ((4*n-k-1).choose (n-k) : ℤ)) : ℚ) = ∑ k ∈ Finset.range (n+1), F n k := by
  push_cast
  exact reflected_sum n hn

end OMA.T386834

namespace OMA.T386834

open scoped BigOperators

lemma sum_extend_zero (t : ℕ → ℕ → ℚ)
    (hz : ∀ m k : ℕ, m < k → t m k = 0)
    (m N : ℕ) (hm : m ≤ N) :
    (∑ k ∈ Finset.range (N + 1), t m k) =
      ∑ k ∈ Finset.range (m + 1), t m k := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkm
  apply hz
  simp only [Finset.mem_range, not_lt] at hkm
  omega

lemma sum_certificate (t : ℕ → ℕ → ℚ)
    (hz : ∀ m k : ℕ, m < k → t m k = 0)
    (n : ℕ) (hn : 2 ≤ n) (c₀ c₁ c₂ : ℚ) (G : ℕ → ℚ)
    (hG₀ : G 0 = 0) (hG₁ : G (n + 1) = 0)
    (hcert : ∀ k : ℕ, k ≤ n →
      c₀ * t n k + c₁ * t (n - 1) k + c₂ * t (n - 2) k =
        G (k + 1) - G k) :
    c₀ * (∑ k ∈ Finset.range (n + 1), t n k) +
      c₁ * (∑ k ∈ Finset.range (n - 1 + 1), t (n - 1) k) +
      c₂ * (∑ k ∈ Finset.range (n - 2 + 1), t (n - 2) k) = 0 := by
  rw [← sum_extend_zero t hz (n - 1) n (by omega),
    ← sum_extend_zero t hz (n - 2) n (by omega)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    (∑ k ∈ Finset.range (n + 1),
        (c₀ * t n k + c₁ * t (n - 1) k + c₂ * t (n - 2) k)) =
        ∑ k ∈ Finset.range (n + 1), (G (k + 1) - G k) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hcert k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)
    _ = 0 := by rw [Finset.sum_range_sub, hG₀, hG₁, sub_self]

lemma sum_ratio_certificate (t : ℕ → ℕ → ℚ)
    (hz : ∀ m k : ℕ, m < k → t m k = 0)
    (n : ℕ) (hn : 2 ≤ n) (c₀ c₁ c₂ : ℚ) (R : ℕ → ℚ)
    (r b : ℕ → ℕ → ℚ)
    (hR₀ : R 0 = 0)
    (hr : ∀ k : ℕ, k ≤ n → t n (k + 1) = t n k * r n k)
    (hb₁ : ∀ k : ℕ, k ≤ n → t (n - 1) k = t n k * b n k)
    (hb₂ : ∀ k : ℕ, k ≤ n → t (n - 2) k = t (n - 1) k * b (n - 1) k)
    (hcert : ∀ k : ℕ, k ≤ n →
      r n k * R (k + 1) - R k =
        c₀ + c₁ * b n k + c₂ * b n k * b (n - 1) k) :
    c₀ * (∑ k ∈ Finset.range (n + 1), t n k) +
      c₁ * (∑ k ∈ Finset.range (n - 1 + 1), t (n - 1) k) +
      c₂ * (∑ k ∈ Finset.range (n - 2 + 1), t (n - 2) k) = 0 := by
  apply sum_certificate t hz n hn c₀ c₁ c₂ (fun k => t n k * R k)
  · simp [hR₀]
  · rw [hz n (n + 1) (by omega), zero_mul]
  intro k hk
  calc
    c₀ * t n k + c₁ * t (n - 1) k + c₂ * t (n - 2) k =
        t n k * (c₀ + c₁ * b n k + c₂ * b n k * b (n - 1) k) := by
      rw [hb₂ k hk, hb₁ k hk]
      ring
    _ = t n k * (r n k * R (k + 1) - R k) := by rw [hcert k hk]
    _ = t n (k + 1) * R (k + 1) - t n k * R k := by rw [hr k hk]; ring

end OMA.T386834

namespace OMA.T386834

lemma repr (n : ℕ) (hn : 1 ≤ n) :
    (OMA.S_oeis_a386834.a n : ℚ) = ∑ k ∈ Finset.range (n + 1), F n k := by
  unfold OMA.S_oeis_a386834.a
  push_cast
  exact reflected_sum n hn

lemma recurrence2 (n : ℕ) (hn : 3 ≤ n) :
    p0 n * (OMA.S_oeis_a386834.a n : ℚ) +
      p1 n * (OMA.S_oeis_a386834.a (n - 1) : ℚ) +
      p2 n * (OMA.S_oeis_a386834.a (n - 2) : ℚ) = 0 := by
  rw [repr n (by omega), repr (n - 1) (by omega), repr (n - 2) (by omega)]
  apply sum_ratio_certificate F F_zero_of_lt n (by omega)
    (p0 n) (p1 n) (p2 n) (fun k => R n k)
    (fun m k => right m k) (fun m k => back m k)
  · simp [R]
  · intro k hk
    exact rightF n k (by omega)
  · intro k hk
    have hc : ((n - 1 : ℕ) : ℚ) + 1 = (n : ℚ) := by
      exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n by omega)
    simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega), hc] using
      backF (n - 1) k (by omega)
  · intro k hk
    have hc : ((n - 2 : ℕ) : ℚ) + 1 = ((n - 1 : ℕ) : ℚ) := by
      exact_mod_cast (show n - 2 + 1 = n - 1 by omega)
    simpa only [show n - 2 + 1 = n - 1 by omega, hc] using
      backF (n - 2) k (by omega)
  · intro k hk
    simpa only [Nat.cast_add, Nat.cast_one,
      Nat.cast_sub (show 1 ≤ n by omega)] using cert n k hn

end OMA.T386834

namespace OMA.T386834

def q0 (n : ℚ) : ℚ :=
  446681331*n^4-1175571522*n^3+828152709*n^2-161975598*n

def q1 (n : ℚ) : ℚ :=
  -1669899251*n^4-26931977989*n^3+131963667975*n^2-188283072995*n+85757456660

def q2 (n : ℚ) : ℚ :=
  -122603852006*n^4+1031852530020*n^3-3310784667858*n^2+4622292150604*n-2330759239080

def q3 (n : ℚ) : ℚ :=
  -120487271424*n^4+939684926976*n^3-2696656153152*n^2+3367511502240*n-1540720742400

set_option maxHeartbeats 800000 in
lemma combine_recurrences (n a₀ a₁ a₂ a₃ : ℚ) (hn : 4 ≤ n)
    (h₀ : p0 n*a₀ + p1 n*a₁ + p2 n*a₂ = 0)
    (h₁ : p0 (n-1)*a₁ + p1 (n-1)*a₂ + p2 (n-1)*a₃ = 0) :
    q0 n*a₀ + q1 n*a₁ + q2 n*a₂ + q3 n*a₃ = 0 := by
  have hd : 77*n^3-347*n^2+516*n-252 ≠ 0 := by
    have hn₀ : 0 ≤ n-4 := by linarith
    have hp : 0 < 77*(n-4)^3 + 577*(n-4)^2 + 1436*(n-4) + 1188 := by positivity
    have he : 77*n^3-347*n^2+516*n-252 =
        77*(n-4)^3 + 577*(n-4)^2 + 1436*(n-4) + 1188 := by ring
    rw [he]
    exact ne_of_gt hp
  apply (mul_eq_zero.mp (show
      (77*n^3-347*n^2+516*n-252) *
        (q0 n*a₀ + q1 n*a₁ + q2 n*a₂ + q3 n*a₃) = 0 from ?_)).resolve_left hd
  calc
    _ = (16543753*n-26995933) * (p0 n*a₀ + p1 n*a₁ + p2 n*a₂) +
        6*(39221117*n-50949760) *
          (p0 (n-1)*a₁ + p1 (n-1)*a₂ + p2 (n-1)*a₃) := by
      unfold q0 q1 q2 q3 p0 p1 p2
      ring
    _ = 0 := by rw [h₀,h₁]; ring

lemma recurrence_three (a : ℕ → ℚ)
    (hrec : ∀ n : ℕ, 3 ≤ n → p0 n*a n + p1 n*a (n-1) + p2 n*a (n-2) = 0)
    (n : ℕ) (hn : 4 ≤ n) :
    q0 n*a n + q1 n*a (n-1) + q2 n*a (n-2) + q3 n*a (n-3) = 0 := by
  apply combine_recurrences n (a n) (a (n-1)) (a (n-2)) (a (n-3)) (by exact_mod_cast hn)
  · exact hrec n (by omega)
  · have h := hrec (n-1) (by omega)
    simpa only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one,
      Nat.sub_sub, show 1+1 = 2 from rfl, show 1+2 = 3 from rfl] using h

end OMA.T386834

open OMA.T386834

theorem OMA.solution : type_of% @OMA.S_oeis_a386834.main := by
  intro n hn
  by_cases h3 : n = 3
  · subst n
    norm_num [OMA.S_oeis_a386834.a, Finset.sum_range_succ, Nat.choose]
  · have hn4 : 4 ≤ n := by omega
    have h := recurrence_three (fun m => (OMA.S_oeis_a386834.a m : ℚ)) recurrence2 n hn4
    unfold q0 q1 q2 q3 at h
    exact_mod_cast h
