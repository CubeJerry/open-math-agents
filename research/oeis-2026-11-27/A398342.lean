import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-!
# Corneth's question on the least qualifying multiple of an odd prime

The A398342 eligibility test below is the prime-power product for the sum
of the radicals of the divisors, divided by the product of the primes.
The proof of this identity also appears as sumrad_prod in the proof of A398343.
We use the substantive reading that q is a prime divisor of the least term.

Source: https://oeis.org/A398342
Credit: @CubeJerry
-/

namespace RadicalLeastMultiple

open Finset

def den (n : ℕ) := ∏ p ∈ n.primeFactors,p

def num (n : ℕ) := ∏ p ∈ n.primeFactors, (n.factorization p*p+1)

def eligible (n : ℕ) := 0<n ∧ den n ∣ num n

def cap : ℕ := 549400309952

def D (p e : ℕ) := if e=0 then 1 else p
def U (p e : ℕ) := if e=0 then 1 else e*p+1
def ld (a b c : ℕ) := D 2 a * D 53 b * D 107 c
def lu (a b c : ℕ) := U 2 a * U 53 b * U 107 c
def lv (a b c : ℕ) := 2^a * 53^b * 107^c

lemma witness : eligible cap ∧ 107 ∣ cap := by
  change (0<cap ∧ den cap ∣ num cap) ∧ 107 ∣ cap
  decide +kernel

lemma small_sources :
    (∀ e : Fin 40, ∀ p ∈ (e.val*2+1).primeFactors, p≤107) ∧
    (∀ e : Fin 7, ∀ p ∈ (e.val*53+1).primeFactors, p≤107) ∧
    (∀ e : Fin 6, ∀ p ∈ (e.val*107+1).primeFactors, p≤107) := by
  decide +kernel

lemma no_low : ∀ a : Fin 40, ∀ b : Fin 7, ∀ c : Fin 6, 0<c.val →
    lv a b c ≤ cap → ¬ ld a b c ∣ lu a b c := by
  decide +kernel

lemma certificate : ∀ a : Fin 13, ∀ b : Fin 3, ∀ c : Fin 3, 0<c.val →
    ∀ r : Fin 4, ∀ s : Fin 5, 2≤r.val → r.val<s.val →
    lv a b c * 108^s.val ≤ cap → ∀ E : Fin 5, 2≤E.val → E.val ≤ 2^(s.val-r.val) →
    lu a b c * E.val * 109^r.val / (ld a b c * 108^r.val) ≤ lu a b c * E.val / ld a b c := by
  decide +kernel

def high (n : ℕ) := n.primeFactors.filter (107<·)

lemma mem_factor (n p : ℕ) : p∈n.primeFactors ↔ n.factorization p ≠ 0 := by
  rw [← n.support_factorization]
  exact Finsupp.mem_support_iff

lemma split_prod {n : ℕ}
    (hl : ∀ q ∈ n.primeFactors, q≤107 → q=2 ∨ q=53 ∨ q=107)
    (f : ℕ → ℕ) :
    (∏ q ∈ n.primeFactors,f q) =
      (if n.factorization 2=0 then 1 else f 2) *
      (if n.factorization 53=0 then 1 else f 53) *
      (if n.factorization 107=0 then 1 else f 107) * ∏ q ∈ high n,f q := by
  classical
  let lo : Finset ℕ := {2,53,107}
  have hs : n.primeFactors = (lo.filter (·∈n.primeFactors)) ∪ high n := by
    ext q
    simp only [mem_union,mem_filter,high]
    constructor
    · intro hq
      by_cases h : 107<q
      · exact Or.inr ⟨hq,h⟩
      · exact Or.inl ⟨by rcases hl q hq (by omega) with h|h|h <;> simp [lo,h],hq⟩
    · rintro (⟨_,hq⟩|⟨hq,_⟩) <;> exact hq
  have hd : Disjoint (lo.filter (·∈n.primeFactors)) (high n) := by
    apply disjoint_left.mpr
    intro p hp hh
    have hlp := (mem_filter.mp hp).1
    have hh' := (mem_filter.mp hh).2
    simp only [lo,mem_insert,mem_singleton] at hlp
    omega
  have hif (q : ℕ) : (if q∈n.primeFactors then f q else 1) =
      (if n.factorization q=0 then 1 else f q) := by
    by_cases h : q∈n.primeFactors
    · simp only [if_pos h,if_neg ((mem_factor n q).mp h)]
    · have hz : n.factorization q=0 := by simpa using (mem_factor n q).not.mp h
      simp only [if_neg h,if_pos hz]
  conv_lhs => rw [hs,prod_union hd,prod_filter]
  simp only [lo,prod_insert (show 2∉({53,107}:Finset ℕ) by decide),
    prod_insert (show 53∉({107}:Finset ℕ) by decide),prod_singleton,hif,mul_assoc]

lemma exponent_bounds {n : ℕ} (hn : 0<n) (hle : n≤cap) :
    n.factorization 2<40 ∧ n.factorization 53<7 ∧ n.factorization 107<6 := by
  have h (p k : ℕ) (hp : 1≤p) (hk : cap<p^k) : n.factorization p<k := by
    by_contra! hh
    have hb := Nat.pow_le_pow_right hp hh
    have hh' := Nat.le_of_dvd hn (Nat.ordProj_dvd n p)
    change p^(n.factorization p) ≤ n at hh'
    omega
  exact ⟨h _ _ (by decide) (by decide),h _ _ (by decide) (by decide),h _ _ (by decide) (by decide)⟩

lemma high_source {n : ℕ} (hn : eligible n) (hle : n≤cap)
    (hl : ∀ q ∈ n.primeFactors, q≤107 → q=2 ∨ q=53 ∨ q=107)
    (hh : (high n).Nonempty) :
    2≤(high n).card ∧ ∃ q ∈ high n, 2≤n.factorization q := by
  let P := (high n).max' hh
  have hP := (high n).max'_mem hh
  change P ∈ high n at hP
  obtain ⟨hp,hbig⟩ := mem_filter.mp hP
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd : P∣den n := dvd_prod_of_mem (fun p => p) hp
  have ht := hd.trans hn.2
  obtain ⟨q,hq,hdq⟩ := (hprime.prime.dvd_finsetProd_iff _).mp ht
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hneq : q≠P := by
    intro he
    subst q
    have h1 : P∣1 := (Nat.dvd_add_iff_right (Nat.dvd_mul_left _ _)).2 hdq
    exact hprime.not_dvd_one h1
  have hqbig : 107<q := by
    by_contra! hs
    obtain ⟨h2,h53,h107⟩ := exponent_bounds hn.1 hle
    have hm : P ∈ (n.factorization q*q+1).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hprime,hdq,by omega⟩
    rcases hl q hq hs with he|he|he <;> subst q
    · exact (not_le_of_gt hbig) (small_sources.1 ⟨_,h2⟩ _ hm)
    · exact (not_le_of_gt hbig) (small_sources.2.1 ⟨_,h53⟩ _ hm)
    · exact (not_le_of_gt hbig) (small_sources.2.2 ⟨_,h107⟩ _ hm)
  have hqH : q∈high n := mem_filter.mpr ⟨hq,hqbig⟩
  have hqle : q<P := lt_of_le_of_ne (le_max' _ _ hqH) hneq
  have hg : 2≤n.factorization q := by
    have hnz := (mem_factor n q).mp hq
    by_contra! hbad
    have heq : n.factorization q=1 := by omega
    rw [heq,one_mul] at hdq
    have hpq := Nat.le_of_dvd (Nat.succ_pos q) hdq
    have hoq := hqp.eq_two_or_odd.resolve_left (by omega)
    have hoP := hprime.eq_two_or_odd.resolve_left (by omega)
    omega
  exact ⟨one_lt_card_iff.mpr ⟨q,P,hqH,hP,hneq⟩,q,hqH,hg⟩

lemma shape {n : ℕ} (hn : 0<n) (hl : ∀ q ∈ n.primeFactors, q≤107 → q=2 ∨ q=53 ∨ q=107) :
    n = lv (n.factorization 2) (n.factorization 53) (n.factorization 107) *
      ∏ p ∈ high n, p^n.factorization p := by
  have he : (∏ p ∈ n.primeFactors,p^n.factorization p) = n := by
    simpa [Finsupp.prod] using Nat.prod_factorization_pow_eq_self hn.ne'
  have hr (q : ℕ) : (if n.factorization q=0 then 1 else q^n.factorization q) = q^n.factorization q := by
    split <;> simp_all
  exact he.symm.trans (by rw [split_prod hl]; simp only [hr,lv])

lemma sizes : ∀ a : Fin 40, ∀ b : Fin 7, ∀ c : Fin 6, 0<c.val →
    (cap < lv a b c * 108^5) ∧
    (lv a b c * 108^3 ≤ cap → a.val<13 ∧ b.val<3 ∧ c.val<3) := by
  decide +kernel

lemma high_bounds (S : Finset ℕ) (e : ℕ→ℕ) (hp : ∀ p ∈ S, 108≤p)
    (he : ∀ p ∈ S, 1≤e p) (hg : ∃ p ∈ S, 2≤e p) :
    let r := S.card
    let s := ∑ p ∈ S,e p
    let E := ∏ p ∈ S,e p
    let d := ∏ p ∈ S,p
    let u := ∏ p ∈ S,(e p*p+1)
    r<s ∧ 2≤E ∧ E≤2^(s-r) ∧ 108^s≤(∏ p ∈ S,p^e p) ∧
      E*d<u ∧ u*108^r ≤ E*d*109^r := by
  dsimp only
  obtain ⟨q,hq,h2⟩ := hg
  have hsum : (∑ p ∈ S,(e p-1)) + S.card = ∑ p ∈ S,e p := by
    calc
      _ = ∑ p ∈ S, ((e p-1)+1) := by simp [sum_add_distrib]
      _ = _ := sum_congr rfl fun p h => Nat.sub_add_cancel (he p h)
  have hone : 1≤ ∑ p ∈ S,(e p-1) := by
    exact (by omega : 1≤e q-1).trans (single_le_sum (fun p _ => Nat.zero_le (e p-1)) hq)
  refine ⟨by omega,?_,?_,?_,?_,?_⟩
  · have hb := prod_le_prod_of_subset_of_one_le (s:={q}) (t:=S) (f:=e)
      (singleton_subset_iff.mpr hq) (fun _ _ => Nat.zero_le _) (fun p h _ => he p h)
    simpa using h2.trans (by simpa using hb : e q ≤ ∏ p ∈ S,e p)
  · rw [show (∑ p ∈ S,e p)-S.card=∑ p ∈ S,(e p-1) by omega,← prod_pow_eq_pow_sum]
    apply prod_le_prod'
    intro p h
    have htwo : e p-1 < 2^(e p-1) := Nat.lt_two_pow_self
    omega
  · rw [← prod_pow_eq_pow_sum]
    exact prod_le_prod' fun p h => Nat.pow_le_pow_left (hp p h) _
  · rw [← prod_mul_distrib]
    apply prod_lt_prod
    · intro p h
      exact Nat.mul_pos (he p h) (by have := hp p h; omega)
    · intro p _; omega
    · exact ⟨q,hq,Nat.lt_succ_self _⟩
  · rw [← prod_const,← prod_mul_distrib,← prod_const,← prod_mul_distrib,← prod_mul_distrib]
    apply prod_le_prod'
    intro p h
    have hbase : 108≤e p*p := by
      calc 108 ≤ 1*p := by simpa using hp p h
           _ ≤ _ := Nat.mul_le_mul_right _ (he p h)
    nlinarith

lemma impossible_good {n : ℕ} (hn : eligible n) (hle : n≤cap) (hd107 : 107∣n)
    (hl : ∀ q ∈ n.primeFactors, q≤107 → q=2 ∨ q=53 ∨ q=107) : False := by
  let a := n.factorization 2
  let b := n.factorization 53
  let c := n.factorization 107
  let S := high n
  let e : ℕ→ℕ := n.factorization
  let r := S.card
  let s := ∑ q ∈ S,e q
  let E := ∏ q ∈ S,e q
  let d := ∏ q ∈ S,q
  let u := ∏ q ∈ S,(e q*q+1)
  have hpos (q) (h : q∈S) : 108≤q := (mem_filter.mp h).2
  have hep (q) (h : q∈S) : 1≤e q :=
    Nat.pos_of_ne_zero ((mem_factor n q).mp (mem_filter.mp h).1)
  have hc : 0<c := Nat.pos_of_ne_zero ((mem_factor n 107).mp
    (Nat.mem_primeFactors.mpr ⟨by decide,hd107,hn.1.ne'⟩))
  obtain ⟨ha,hb,hc'⟩ := exponent_bounds hn.1 hle
  change a<40 at ha
  change b<7 at hb
  change c<6 at hc'
  have hD : den n = ld a b c*d := split_prod hl (fun p => p)
  have hU : num n = lu a b c*u := split_prod hl (fun p => n.factorization p*p+1)
  have hV : n = lv a b c*(∏ q ∈ S,q^e q) := shape hn.1 hl
  obtain ⟨m,hm⟩ := hn.2
  rw [hD,hU] at hm
  by_cases hs : S.Nonempty
  · obtain ⟨hr,hg⟩ := high_source hn hle hl hs
    obtain ⟨hrs,hE,hEmax,hv,hsmall,hlarge⟩ := high_bounds S e hpos hep hg
    change 2≤r at hr
    change r<s at hrs
    change 2≤E at hE
    change E≤2^(s-r) at hEmax
    change 108^s≤_ at hv
    change E*d<u at hsmall
    change u*108^r≤E*d*109^r at hlarge
    have hcap : lv a b c * 108^s≤cap :=
      (Nat.mul_le_mul_left _ hv).trans (hV.symm ▸ hle)
    obtain ⟨h5,h3⟩ := sizes ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc'⟩ hc
    have hpow {i j : ℕ} (h : i≤j) : lv a b c * 108^i ≤ lv a b c * 108^j :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) h)
    have hs5 : s<5 := by by_contra! h; exact (not_le_of_gt h5) ((hpow h).trans hcap)
    obtain ⟨ha',hb',hc''⟩ := h3 ((hpow (by omega)).trans hcap)
    have hE5 : E<5 := by
      have h2 : 2^(s-r) ≤ 2^2 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have pack := certificate ⟨a,ha'⟩ ⟨b,hb'⟩ ⟨c,hc''⟩ hc
      ⟨r,by omega⟩ ⟨s,hs5⟩ hr hrs hcap ⟨E,hE5⟩ hE hEmax
    change lu a b c * E * 109^r / (ld a b c * 108^r) ≤ lu a b c * E / ld a b c at pack
    have hld : 0<ld a b c := by
      have hd (p j : ℕ) (hp : 0<p) : 0<D p j := by unfold D;split <;> omega
      unfold ld
      exact Nat.mul_pos (Nat.mul_pos (hd _ _ (by decide)) (hd _ _ (by decide))) (hd _ _ (by decide))
    have hlu : 0<lu a b c := by
      have hu (p j : ℕ) : 0<U p j := by unfold U;split <;> omega
      unfold lu
      exact Nat.mul_pos (Nat.mul_pos (hu _ _) (hu _ _)) (hu _ _)
    have hdpos : 0<d := prod_pos fun q h => by have := hpos q h; omega
    have hlower : lu a b c * E / ld a b c < m := by
      apply (Nat.div_lt_iff_lt_mul hld).mpr
      apply Nat.lt_of_mul_lt_mul_right (a:=d)
      calc
        _ = lu a b c*(E*d) := by ring
        _ < lu a b c*u := Nat.mul_lt_mul_of_pos_left hsmall hlu
        _ = _ := by rw [hm];ring
    have hupper : m ≤ lu a b c * E * 109^r / (ld a b c * 108^r) := by
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos hld (by positivity))).mpr
      apply Nat.le_of_mul_le_mul_right (c:=d) _ hdpos
      calc
        _ = (ld a b c*d*m)*108^r := by ring
        _ = lu a b c * (u*108^r) := by rw [← hm];ring
        _ ≤ lu a b c * (E*d*109^r) := Nat.mul_le_mul_left _ hlarge
        _ = _ := by ring
    omega
  · have hS := not_nonempty_iff_eq_empty.mp hs
    have hU1 : u=1 := by simp [u,hS]
    have hD1 : d=1 := by simp [d,hS]
    simp only [hU1,hD1,mul_one] at hm
    simp only [hS,prod_empty,mul_one] at hV
    exact no_low ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc'⟩ hc (hV ▸ hle) ⟨m,hm⟩

theorem counterexample : ¬(∀ p : ℕ, p.Prime → 2<p → ∀ t : ℕ,
    eligible t → p ∣ t → (∀ s, eligible s → p ∣ s → t≤s) →
    ∀ q : ℕ, q.Prime → q ∣ t → q<p → q ∣ p-1) := by
  classical
  intro hall
  have hex : ∃ t, eligible t ∧ 107 ∣ t := ⟨cap,witness⟩
  let t := Nat.find hex
  have ht : eligible t ∧ 107∣t := Nat.find_spec hex
  have hmin : ∀ s, eligible s → 107∣s → t≤s := fun _ hs hd => Nat.find_min' hex ⟨hs,hd⟩
  have hcap := hmin cap witness.1 witness.2
  apply impossible_good ht.1 hcap ht.2
  intro q hq hle
  rcases eq_or_lt_of_le hle with he|hlt
  · exact Or.inr (Or.inr he)
  have hp := Nat.prime_of_mem_primeFactors hq
  have hd := hall 107 (by decide) (by decide) t ht.1 ht.2 hmin q hp
    (Nat.dvd_of_mem_primeFactors hq) hlt
  have hmem : q∈(106:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hd,by decide⟩
  have hf : (106:ℕ).primeFactors = {2,53} := by
    rw [show (106:ℕ)=2*53 by decide,Nat.primeFactors_mul (by decide) (by decide),
      Nat.prime_two.primeFactors,(show Nat.Prime 53 by decide).primeFactors]
    simp
  rw [hf] at hmem
  simp only [mem_insert,mem_singleton] at hmem
  tauto

end RadicalLeastMultiple
