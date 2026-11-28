import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! An artificial sequence, not the progression-free extremal function. -/
namespace Erdos142SparseDrops

def mass (n : ℕ) : ℕ := 2 ^ (n - Nat.sqrt n)
def slowSteps (J : ℕ) : Finset ℕ :=
  (Finset.range J).filter (fun n => Nat.sqrt (n+1) ≠ Nat.sqrt n)

theorem mass_pos (n : ℕ) : 0 < mass n := by unfold mass; positivity

theorem jump_square {n : ℕ} (h : Nat.sqrt (n+1) ≠ Nat.sqrt n) :
    Nat.sqrt (n+1)^2 = n+1 := by
  have hm := Nat.sqrt_le_sqrt (show n ≤ n+1 by omega)
  have hu := Nat.sqrt_le' (n+1)
  have hl : n < Nat.sqrt (n+1)^2 := by
    by_contra hn
    have he := Nat.le_sqrt'.mpr (show Nat.sqrt (n+1)^2 ≤ n by omega)
    omega
  omega

theorem normal_step {n : ℕ} (h : Nat.sqrt (n+1) = Nat.sqrt n) :
    mass (n+1) = 2 * mass n := by
  have hb := Nat.sqrt_le_self n
  unfold mass
  rw [h, show n+1-Nat.sqrt n = (n-Nat.sqrt n)+1 by omega, pow_succ]
  omega

theorem slow_step {n : ℕ} (h : Nat.sqrt (n+1) ≠ Nat.sqrt n) :
    mass (n+1) = mass n := by
  have hm := Nat.sqrt_le_sqrt (show n ≤ n+1 by omega)
  have hu := Nat.sqrt_succ_le_succ_sqrt n
  change Nat.sqrt (n+1) ≤ Nat.sqrt n+1 at hu
  have hb := Nat.sqrt_le_self n
  unfold mass
  congr 1
  omega

theorem slow_step_count (J : ℕ) : (slowSteps J).card ≤ Nat.sqrt J := by
  have inj : Set.InjOn (fun n => Nat.sqrt (n+1)) (slowSteps J : Set ℕ) := by
    intro n hn m hm he
    have sn := jump_square (Finset.mem_filter.mp hn).2
    have sm := jump_square (Finset.mem_filter.mp hm).2
    change Nat.sqrt (n+1) = Nat.sqrt (m+1) at he
    rw [he] at sn
    omega
  have sub : (slowSteps J).image (fun n => Nat.sqrt (n+1)) ⊆
      Finset.Icc 1 (Nat.sqrt J) := by
    intro q hq
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hn,_⟩ := Finset.mem_filter.mp hn
    have hlt := Finset.mem_range.mp hn
    apply Finset.mem_Icc.mpr
    exact ⟨Nat.sqrt_pos.mpr (by omega), Nat.sqrt_le_sqrt (by omega)⟩
  calc
    (slowSteps J).card = ((slowSteps J).image (fun n => Nat.sqrt (n+1))).card :=
      (Finset.card_image_of_injOn inj).symm
    _ ≤ (Finset.Icc 1 (Nat.sqrt J)).card := Finset.card_le_card sub
    _ = Nat.sqrt J := by simp

theorem slow_step_fraction {M J : ℕ} (h : M^2 ≤ J) :
    M * (slowSteps J).card ≤ J := by
  have hm := Nat.le_sqrt'.mpr h
  have hc := slow_step_count J
  have hs := Nat.sqrt_le' J
  nlinarith

theorem sqrt_before_square {j : ℕ} (hj : 0 < j) :
    Nat.sqrt (j^2-1) = j-1 := by
  apply (Nat.eq_sqrt'.mpr ?_).symm
  have hjs : 1 ≤ j^2 := by nlinarith
  have hs : j^2-1+1 = j^2 := by omega
  have hj1 : j-1+1 = j := by omega
  constructor <;> nlinarith

theorem square_drop {j : ℕ} (hj : 0 < j) :
    mass (j^2) = mass (j^2-1) := by
  have hjs : j^2-1+1 = j^2 := by
    have : 1 ≤ j^2 := by nlinarith
    omega
  have h := slow_step (n := j^2-1) (by
    rw [hjs, Nat.sqrt_eq', sqrt_before_square hj]
    omega)
  simpa only [hjs] using h

theorem square_recovery {j : ℕ} (hj : 0 < j) :
    mass (j^2+1) = 2 * mass (j^2) := by
  apply normal_step
  rw [Nat.sqrt_eq', Nat.sqrt_add_eq' j (by omega : 1 ≤ j+j)]

theorem arbitrarily_late_drops (N : ℕ) :
    ∃ n ≥ N, mass (n+1) = mass n := by
  refine ⟨(N+1)^2-1, ?_, ?_⟩
  · have : N+1 ≤ (N+1)^2 := by nlinarith
    omega
  · have he : (N+1)^2-1+1 = (N+1)^2 := by
      have : 0 < (N+1)^2 := by positivity
      omega
    simpa only [he] using square_drop (by omega : 0 < N+1)

theorem ratios_fail_eventual_closeness :
    ¬ ∃ N : ℕ, ∀ n ≥ N, |(mass (n+1) : ℚ)/mass n-2| < 1/2 := by
  rintro ⟨N,hN⟩
  obtain ⟨n,hn,he⟩ := arbitrarily_late_drops N
  have h := hN n hn
  have hp : (mass n : ℚ) ≠ 0 := by exact_mod_cast (mass_pos n).ne'
  rw [he, div_self hp] at h
  norm_num at h

#print axioms slow_step_count
#print axioms slow_step_fraction
#print axioms square_drop
#print axioms square_recovery
#print axioms ratios_fail_eventual_closeness
end Erdos142SparseDrops
