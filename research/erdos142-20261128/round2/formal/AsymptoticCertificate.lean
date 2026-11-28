import BlockCertificate

/-!
Generic asymptotic transfer for certified two-dimensional torus blocks.
Adapted from 555tery's pinned Geometry.lean proof by exposing the block density
and potential bound as parameters. No new geometric density is asserted here.
-/

namespace Erdos142BlockCertificate
open QuandleResearch.Erdos142
noncomputable section

/-- Every sufficiently large prime has a certified block of uniform density,
with a potential height bounded independently of the prime. -/
def UniformDensity (ρ : ℝ) (H p0 : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p0 ≤ p → ∃ C : Certificate p,
    C.height ≤ (H:ℝ) ∧ ρ*(p:ℝ)^2 ≤ (C.block.card:ℝ)

set_option maxHeartbeats 800000 in
theorem roth_integer_parameters (ρ : ℝ) (H p0 : ℕ)
    (family : UniformDensity ρ H p0) (hρ : 0 < ρ) (N m t : ℕ) (hm : 0 < m) (ht : 0 < t)
    (hNt : N < (t * t)^m) :
    (N : ℝ) * ρ^m <
      (128 : ℝ) * ((m : ℝ) * H + 1) * (t : ℝ)^2 *
        ((rothNumberNat N : ℝ) + 2) := by
  obtain ⟨p, hpbound, hprime⟩ := Nat.exists_infinite_primes
    (max (max N p0) (8 * t))
  let _ : Fact p.Prime := ⟨hprime⟩
  have hN : N ≤ p := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hpbound
  have hp : p0 ≤ p :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hpbound
  have hpt : 8 * t ≤ p := le_trans (le_max_right _ _) hpbound
  have hp0 : 0 < p := hprime.pos
  obtain ⟨B,hBheight,hBdensity⟩ := family p hprime hp
  let R := p / (4 * t)
  let L := 128 * (m * H + 1) * t^2
  let G := (p * p)^m
  let A := B.block.card^m
  let J := A / L
  let K := (N * J) / G
  let w : ℝ := 1 / (128 * (t : ℝ)^2)
  have hL : 0 < L := by dsimp [L]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hR := div_mul_bounds p (4 * t) (by omega)
  have hrlo : p ≤ 8 * t * R := by
    change R * (4 * t) ≤ p ∧ p < R * (4 * t) + 4 * t at hR
    nlinarith [hR.2, hpt]
  have hrt : (2 * R + 1) * t ≤ p := by
    change R * (4 * t) ≤ p ∧ p < R * (4 * t) + 4 * t at hR
    nlinarith [hR.1, hpt]
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast ht
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp0
  have hw : 0 < w := by dsimp [w]; positivity
  have hwR : 2 * w ≤ ((R : ℝ) / (p : ℝ))^2 := by
    have hr : (p : ℝ) ≤ 8 * (t : ℝ) * (R : ℝ) := by exact_mod_cast hrlo
    have hdiv : 1 / (8 * (t : ℝ)) ≤ (R : ℝ) / (p : ℝ) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 8 * (t : ℝ)) hp').2
      linarith
    have hs := mul_le_mul hdiv hdiv (by positivity) (by positivity)
    calc
      2 * w = (1 / (8 * (t : ℝ))) * (1 / (8 * (t : ℝ))) := by
        dsimp [w]
        field_simp
        ring
      _ ≤ ((R : ℝ) / (p : ℝ))^2 := by simpa [pow_two] using hs
  have hwidth : (m : ℝ) * H < (L : ℝ) * w := by
    have he : (L : ℝ) * w = (m : ℝ) * H + 1 := by
      dsimp [L, w]
      push_cast
      field_simp
    linarith
  have hD : N * ((2 * R + 1) * (2 * R + 1))^m < G := by
    have hprod := Nat.mul_le_mul hrt hrt
    have hbase : (t * t) * ((2 * R + 1) * (2 * R + 1)) ≤ p * p := by
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprod
    calc
      _ < (t * t)^m * ((2 * R + 1) * (2 * R + 1))^m :=
        Nat.mul_lt_mul_of_pos_right hNt (by positivity)
      _ = ((t * t) * ((2 * R + 1) * (2 * R + 1)))^m := by simp only [mul_pow]
      _ ≤ G := Nat.pow_le_pow_left hbase m
  have hJ := div_mul_bounds A L hL
  have hK := div_mul_bounds (N * J) G hG
  have hJ' : L * J ≤ A := by simpa [J, Nat.mul_comm] using hJ.1
  have hK' : G * K ≤ N * J := by simpa [K, Nat.mul_comm] using hK.1
  have hBwidth : (m:ℝ)*B.height < (L:ℝ)*w :=
    (mul_le_mul_of_nonneg_left hBheight (Nat.cast_nonneg m)).trans_lt hwidth
  have hr := roth_finite_parameters p m R N L J K B hN hL w hw hwR hBwidth hD hJ' hK'
  have hNG : N ≤ G := by
    have hpp : p ≤ p * p := by nlinarith
    have hpow : p * p ≤ (p * p)^m := by
      simpa using (pow_le_pow_right' (show 1 ≤ p * p by exact Nat.succ_le_of_lt (Nat.mul_pos hp0 hp0))
        (show 1 ≤ m by omega))
    exact hN.trans (hpp.trans hpow)
  have hden' : ρ*((p:ℝ)*p) ≤ (B.block.card:ℝ) := by
    nlinarith [hBdensity]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ρ * ((p : ℝ) * p)) hden' m
  have hAG : ρ^m * (G : ℝ) ≤ (A : ℝ) := by
    dsimp [A, G]
    push_cast
    rw [← mul_pow]
    exact hpow
  have hA : (A : ℝ) < (L : ℝ) * ((J : ℝ) + 1) := by
    have hh : (A : ℝ) < (J : ℝ) * (L : ℝ) + (L : ℝ) := by
      exact_mod_cast hJ.2
    nlinarith
  have hNJ : (N : ℝ) * (J : ℝ) < (G : ℝ) * ((K : ℝ) + 1) := by
    have hh : (N : ℝ) * (J : ℝ) < (K : ℝ) * (G : ℝ) + (G : ℝ) := by
      exact_mod_cast hK.2
    nlinarith
  have hNG' : (N : ℝ) ≤ (G : ℝ) := by exact_mod_cast hNG
  have hKr : (K : ℝ) ≤ (rothNumberNat N : ℝ) := by exact_mod_cast hr
  have hLp : 0 < (L : ℝ) := by exact_mod_cast hL
  have hGp : 0 < (G : ℝ) := by exact_mod_cast hG
  have hnp : 0 ≤ (N : ℝ) := by positivity
  have hN0 : N = 0 ∨ 0 < N := by omega
  rcases hN0 with hzero | hpos
  · subst N
    simp only [Nat.cast_zero, zero_mul]
    positivity
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hpos
  have hmain : (N : ℝ) * ρ^m * (G : ℝ) <
      (L : ℝ) * ((rothNumberNat N : ℝ) + 2) * (G : ℝ) := by
    calc
      _ ≤ (N : ℝ) * (A : ℝ) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hAG hnp
      _ < (N : ℝ) * ((L : ℝ) * ((J : ℝ) + 1)) :=
        mul_lt_mul_of_pos_left hA hNp
      _ = (L : ℝ) * ((N : ℝ) * (J : ℝ) + (N : ℝ)) := by ring
      _ < (L : ℝ) * ((G : ℝ) * ((K : ℝ) + 2)) := by
        apply mul_lt_mul_of_pos_left _ hLp
        nlinarith
      _ ≤ (L : ℝ) * ((G : ℝ) * ((rothNumberNat N : ℝ) + 2)) := by
        gcongr
      _ = _ := by ring
  have hfinal : (N : ℝ) * ρ^m <
      (L : ℝ) * ((rothNumberNat N : ℝ) + 2) := by
    by_contra hn
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_right (le_of_not_gt hn) hGp.le)) hmain
  dsimp [L] at hfinal
  push_cast at hfinal
  exact hfinal



theorem roth_exp_parameters (ρ : ℝ) (H p0 : ℕ)
    (family : UniformDensity ρ H p0) (hρ : 0 < ρ) (N m : ℕ) (hN : 1 ≤ N) (hm : 0 < m) :
    (N : ℝ) * Real.exp (-((m : ℝ) * Real.log (ρ⁻¹) +
      Real.log (N : ℝ) / (m : ℝ))) <
      512 * ((m : ℝ) * H + 1) * ((rothNumberNat N : ℝ) + 2) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hn1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  let v : ℝ := Real.log (N : ℝ) / (2 * (m : ℝ))
  let E : ℝ := Real.exp v
  have hv : 0 ≤ v := div_nonneg (Real.log_nonneg hn1) (by positivity)
  have hE : 1 ≤ E := Real.one_le_exp hv
  let t : ℕ := ⌊E⌋₊ + 1
  have ht : 0 < t := by dsimp [t]; omega
  have htl : E < (t : ℝ) := by
    dsimp [t]
    push_cast
    exact Nat.lt_floor_add_one E
  have htu : (t : ℝ) ≤ 2 * E := by
    have hh := Nat.floor_le (show 0 ≤ E by linarith)
    dsimp [t]
    push_cast
    linarith
  have hEpow : (E * E)^m = (N : ℝ) := by
    dsimp [E]
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    have he : (m : ℝ) * (v + v) = Real.log (N : ℝ) := by
      dsimp [v]
      field_simp
      ring
    rw [he, Real.exp_log hNp]
  have hbase : E * E < (t : ℝ) * (t : ℝ) := by
    nlinarith [mul_pos (show 0 < (t : ℝ) - E by linarith)
      (show 0 < (t : ℝ) + E by linarith)]
  have hNt' : (N : ℝ) < ((t : ℝ) * (t : ℝ))^m := by
    rw [← hEpow]
    exact pow_lt_pow_left₀ hbase (by positivity) (Nat.ne_of_gt hm)
  have hNt : N < (t * t)^m := by exact_mod_cast hNt'
  have h := roth_integer_parameters ρ H p0 family hρ N m t hm ht hNt
  have ht2 : (t : ℝ)^2 ≤ 4 * Real.exp (Real.log (N : ℝ) / (m : ℝ)) := by
    have hh := mul_le_mul htu htu (by positivity) (by positivity)
    have he : E * E = Real.exp (Real.log (N : ℝ) / (m : ℝ)) := by
      dsimp [E]
      rw [← Real.exp_add]
      congr 1
      dsimp [v]
      ring
    nlinarith
  let a : ℝ := Real.log (ρ⁻¹)
  have hden : Real.exp (-a) = ρ := by
    dsimp [a]
    rw [Real.exp_neg, Real.exp_log (inv_pos.mpr hρ), inv_inv]
  have hpow : ρ^m = Real.exp (-((m : ℝ) * a)) := by
    rw [← hden, ← Real.exp_nat_mul]
    congr 1
    ring
  have hnon : 0 ≤ (128 : ℝ) * ((m : ℝ) * H + 1) *
      ((rothNumberNat N : ℝ) + 2) := by positivity
  have hh : (N : ℝ) * Real.exp (-((m : ℝ) * a)) <
      512 * ((m : ℝ) * H + 1) * ((rothNumberNat N : ℝ) + 2) *
      Real.exp (Real.log (N : ℝ) / (m : ℝ)) := by
    rw [hpow] at h
    calc
      _ < 128 * ((m : ℝ) * H + 1) * (t : ℝ)^2 *
          ((rothNumberNat N : ℝ) + 2) := h
      _ = (128 * ((m : ℝ) * H + 1) *
          ((rothNumberNat N : ℝ) + 2)) * (t : ℝ)^2 := by ring
      _ ≤ (128 * ((m : ℝ) * H + 1) *
          ((rothNumberNat N : ℝ) + 2)) *
          (4 * Real.exp (Real.log (N : ℝ) / (m : ℝ))) :=
        mul_le_mul_of_nonneg_left ht2 hnon
      _ = _ := by ring
  have hpos := Real.exp_pos (-(Real.log (N : ℝ) / (m : ℝ)))
  have hmul := mul_lt_mul_of_pos_right hh hpos
  have hcancel : Real.exp (Real.log (N : ℝ) / (m : ℝ)) *
      Real.exp (-(Real.log (N : ℝ) / (m : ℝ))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hleft : Real.exp (-((m : ℝ) * a)) *
      Real.exp (-(Real.log (N : ℝ) / (m : ℝ))) =
      Real.exp (-((m : ℝ) * a + Real.log (N : ℝ) / (m : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [mul_assoc, hleft, hcancel, mul_one, a] using hmul

theorem roth_sqrt_bound (ρ : ℝ) (H p0 : ℕ)
    (family : UniformDensity ρ H p0) (hρ : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * Real.exp (-(2 * Real.sqrt (Real.log (ρ⁻¹)) *
      Real.sqrt (Real.log (N : ℝ)) + Real.log (ρ⁻¹))) <
      512 * (H * (Real.sqrt (Real.log (N : ℝ)) /
        Real.sqrt (Real.log (ρ⁻¹)) + 1) + 1) *
        ((rothNumberNat N : ℝ) + 2) := by
  let a : ℝ := Real.log (ρ⁻¹)
  let b : ℝ := Real.sqrt a
  let u : ℝ := Real.sqrt (Real.log (N : ℝ))
  have ha : 0 < a := Real.log_pos ((one_lt_inv₀ hρ).mpr hρ1)
  have hb : 0 < b := Real.sqrt_pos.2 ha
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hb2 : b^2 = a := Real.sq_sqrt ha.le
  have hu2 : u^2 = Real.log (N : ℝ) :=
    Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast hN))
  let m : ℕ := ⌊u / b⌋₊ + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hml : u / b < (m : ℝ) := by
    dsimp [m]
    push_cast
    exact Nat.lt_floor_add_one _
  have hmu : (m : ℝ) ≤ u / b + 1 := by
    have hh := Nat.floor_le (div_nonneg hu hb.le)
    dsimp [m]
    push_cast
    linarith
  have hmb : u ≤ (m : ℝ) * b := ((div_lt_iff₀ hb).mp hml).le
  have hma : (m : ℝ) * a ≤ b * u + a := by
    have hh := (le_div_iff₀ hb).mp (show (m : ℝ) - 1 ≤ u / b by linarith)
    calc
      (m : ℝ) * a = ((m : ℝ) - 1) * b * b + a := by rw [← hb2]; ring
      _ ≤ u * b + a := by
        linarith [mul_le_mul_of_nonneg_right hh hb.le]
      _ = b * u + a := by ring
  have hlog : Real.log (N : ℝ) / (m : ℝ) ≤ b * u := by
    apply (div_le_iff₀ hm').2
    calc
      Real.log (N : ℝ) = u * u := by rw [← hu2, pow_two]
      _ ≤ ((m : ℝ) * b) * u := mul_le_mul_of_nonneg_right hmb hu
      _ = b * u * (m : ℝ) := by ring
  have hopt : (m : ℝ) * a + Real.log (N : ℝ) / (m : ℝ) ≤
      2 * b * u + a := by linarith
  have h := roth_exp_parameters ρ H p0 family hρ N m hN hm
  change (N : ℝ) * Real.exp (-((m : ℝ) * a +
    Real.log (N : ℝ) / (m : ℝ))) < _ at h
  change (N : ℝ) * Real.exp (-(2 * b * u + a)) <
    512 * (H * (u / b + 1) + 1) * ((rothNumberNat N : ℝ) + 2)
  calc
    _ ≤ (N : ℝ) * Real.exp (-((m : ℝ) * a +
        Real.log (N : ℝ) / (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    _ < 512 * ((m : ℝ) * H + 1) * ((rothNumberNat N : ℝ) + 2) := h
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hmH := mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg H (α := ℝ))
      nlinarith only [hmH]

theorem roth_eventual_of_constant (ρ : ℝ) (H p0 : ℕ)
    (family : UniformDensity ρ H p0) (hρ : 0 < ρ) (hρ1 : ρ < 1) (C : ℝ)
    (hC : 2 * Real.sqrt (Real.log (ρ⁻¹)) < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log (N : ℝ))) ≤
        (rothNumberNat N : ℝ) := by
  let a : ℝ := Real.log (ρ⁻¹)
  let b : ℝ := Real.sqrt a
  let d : ℝ := C - 2 * b
  let M : ℝ := 1536 * (H * (1 / b + 1) + 1) * Real.exp a
  have ha : 0 < a := Real.log_pos ((one_lt_inv₀ hρ).mpr hρ1)
  have hb : 0 < b := Real.sqrt_pos.2 ha
  have hd : 0 < d := by dsimp [d, b, a]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨U, hU, hdom⟩ := exp_dominates_linear d M hd hM
  let N₀ : ℕ := ⌊Real.exp (U^2)⌋₊ + 1
  refine ⟨N₀, ?_⟩
  intro N hN
  have hN₀ : 0 < N₀ := by dsimp [N₀]; omega
  have hN1 : 1 ≤ N := by omega
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNN : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hexp : Real.exp (U^2) < (N₀ : ℝ) := by
    dsimp [N₀]
    push_cast
    exact Nat.lt_floor_add_one _
  have hlog : U^2 ≤ Real.log (N : ℝ) :=
    (Real.le_log_iff_exp_le hNp).2 (le_trans hexp.le hNN)
  let u : ℝ := Real.sqrt (Real.log (N : ℝ))
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = Real.log (N : ℝ) :=
    Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast hN1))
  have huU : U ≤ u := by
    by_contra hn
    have hpos : 0 < U - u := by linarith
    have hpos' : 0 < U + u := by linarith
    nlinarith [mul_pos hpos hpos']
  have hu1 : 1 ≤ u := le_trans hU huU
  have hD := hdom u huU
  have hr : 1 ≤ (rothNumberNat N : ℝ) := by exact_mod_cast roth_at_least_one N hN1
  have hr0 : 0 ≤ (rothNumberNat N : ℝ) := by positivity
  have hbase := roth_sqrt_bound ρ H p0 family hρ hρ1 N hN1
  change (N : ℝ) * Real.exp (-(2 * b * u + a)) <
    512 * (H * (u / b + 1) + 1) * ((rothNumberNat N : ℝ) + 2) at hbase
  have hpoly : 512 * (H * (u / b + 1) + 1) ≤
      512 * (H * (1 / b + 1) + 1) * u := by
    have hquot : u / b = (1 / b) * u := by ring
    rw [hquot]
    nlinarith [mul_nonneg (show 0 ≤ (1 / b : ℝ) by positivity)
      (show 0 ≤ u - 1 by linarith)]
  have hbase' : (N : ℝ) * Real.exp (-(2 * b * u + a)) <
      1536 * (H * (1 / b + 1) + 1) * u * (rothNumberNat N : ℝ) := by
    calc
      _ < 512 * (H * (u / b + 1) + 1) * ((rothNumberNat N : ℝ) + 2) := hbase
      _ ≤ 512 * (H * (1 / b + 1) + 1) * u *
          (3 * (rothNumberNat N : ℝ)) :=
        mul_le_mul hpoly (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have hmult := mul_lt_mul_of_pos_right hbase' (Real.exp_pos a)
  have hleft : Real.exp (-(2 * b * u + a)) * Real.exp a =
      Real.exp (-(2 * b * u)) := by rw [← Real.exp_add]; congr 1; ring
  have hmain : (N : ℝ) * Real.exp (-(2 * b * u)) <
      Real.exp (d * u) * (rothNumberNat N : ℝ) := by
    calc
      _ = (N : ℝ) * (Real.exp (-(2 * b * u + a)) * Real.exp a) :=
        congrArg (fun x : ℝ => (N : ℝ) * x) hleft.symm
      _ = ((N : ℝ) * Real.exp (-(2 * b * u + a))) * Real.exp a :=
        (mul_assoc _ _ _).symm
      _ < (1536 * (H * (1 / b + 1) + 1) * u *
          (rothNumberNat N : ℝ)) * Real.exp a := hmult
      _ = (M * u) * (rothNumberNat N : ℝ) := by dsimp [M]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hD hr0
  change (N : ℝ) * Real.exp (-C * u) ≤ _
  have hc : Real.exp (-C * u) * Real.exp (d * u) =
      Real.exp (-(2 * b * u)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [d]
    ring
  apply (mul_le_mul_iff_of_pos_right (Real.exp_pos (d * u))).mp
  calc
    _ = (N : ℝ) * (Real.exp (-C * u) * Real.exp (d * u)) := mul_assoc _ _ _
    _ = (N : ℝ) * Real.exp (-(2 * b * u)) :=
      congrArg (fun x : ℝ => (N : ℝ) * x) hc
    _ ≤ Real.exp (d * u) * (rothNumberNat N : ℝ) := hmain.le
    _ = _ := mul_comm _ _


#print axioms roth_integer_parameters
#print axioms roth_sqrt_bound
#print axioms roth_eventual_of_constant
end
end Erdos142BlockCertificate
