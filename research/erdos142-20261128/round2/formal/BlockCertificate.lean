import ClaimGeometryPinned

/-!
An adaptable finite certificate interface for improved torus blocks.
The shell, slope, and interval transfer below reuse 555tery's independently
replayed machinery. This interface does not claim a new density constant.
-/

namespace Erdos142BlockCertificate

open QuandleResearch.Erdos142

noncomputable section

/-- A finite block certificate records only the facts needed by tensorization
and the interval transfer. Its geometric content is the last inequality. -/
structure Certificate (p : ℕ) where
  block : Finset (ZMod p × ZMod p)
  X : ZMod p × ZMod p → ℤ
  Y : ZMod p × ZMod p → ℤ
  F : ZMod p × ZMod p → ℝ
  height : ℝ
  lift : ∀ v ∈ block, (X v : ZMod p) = v.1 ∧ (Y v : ZMod p) = v.2
  bounds : ∀ v ∈ block, 0 ≤ F v ∧ F v ≤ height
  gap : ∀ x ∈ block, ∀ y ∈ block, ∀ z ∈ block, x+z=y+y →
    (((X z-X x : ℤ):ℝ)/(p:ℝ))^2 + (((Y z-Y x : ℤ):ℝ)/(p:ℝ))^2 ≤
      F x+F z-2*F y

/-- A certificate implies the short-difference property for every thin shell
of every tensor power. -/
theorem shell_shortBox (p m R : ℕ) [NeZero p] (hp : 0 < p)
    (C : Certificate p) (S : Finset (Fin m → ZMod p × ZMod p))
    (hS : ∀ v ∈ S, ∀ i, v i ∈ C.block) (b w : ℝ)
    (hw : 2*w ≤ ((R:ℝ)/(p:ℝ))^2)
    (hF : ∀ v ∈ S, b ≤ ∑ i, C.F (v i) ∧ (∑ i, C.F (v i)) ≤ b+w) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x+z=y+y → z-x ∈ shortBox p m R := by
  classical
  intro x hx y hy z hz hAP
  let distance : Fin m → ℝ := fun i =>
    (((C.X (z i)-C.X (x i):ℤ):ℝ)/(p:ℝ))^2+
      (((C.Y (z i)-C.Y (x i):ℤ):ℝ)/(p:ℝ))^2
  have total : (∑ i, distance i) ≤ 2*w := by
    have gap : (∑ i, distance i) ≤
        (∑ i, C.F (x i))+(∑ i, C.F (z i))-2*(∑ i, C.F (y i)) := by
      calc
        _ ≤ ∑ i, (C.F (x i)+C.F (z i)-2*C.F (y i)) := by
          apply Finset.sum_le_sum
          intro i _
          exact C.gap (x i) (hS x hx i) (y i) (hS y hy i)
            (z i) (hS z hz i) (congrFun hAP i)
        _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
    linarith [(hF x hx).2,(hF y hy).1,(hF z hz).2]
  apply Fintype.mem_piFinset.mpr
  intro i
  have one : distance i ≤ ∑ j, distance j :=
    Finset.single_le_sum (f := distance) (fun j _ => by dsimp [distance];positivity)
      (Finset.mem_univ i)
  have sx : (((C.X (z i)-C.X (x i):ℤ):ℝ)/(p:ℝ))^2 ≤ ((R:ℝ)/(p:ℝ))^2 := by
    dsimp only [distance] at one
    nlinarith [sq_nonneg ((((C.Y (z i)-C.Y (x i):ℤ):ℝ)/(p:ℝ)))]
  have sy : (((C.Y (z i)-C.Y (x i):ℤ):ℝ)/(p:ℝ))^2 ≤ ((R:ℝ)/(p:ℝ))^2 := by
    dsimp only [distance] at one
    nlinarith [sq_nonneg ((((C.X (z i)-C.X (x i):ℤ):ℝ)/(p:ℝ)))]
  have bx := normalized_square_to_int_bound hp sx
  have by' := normalized_square_to_int_bound hp sy
  have mx := mem_shortResidues (p := p) bx.1 bx.2
  have my := mem_shortResidues (p := p) by'.1 by'.2
  push_cast at mx my
  rw [(C.lift (z i) (hS z hz i)).1,(C.lift (x i) (hS x hx i)).1] at mx
  rw [(C.lift (z i) (hS z hz i)).2,(C.lift (x i) (hS x hx i)).2] at my
  exact Finset.mem_product.mpr ⟨mx,my⟩

/-- Generic bridge from a certified finite two-dimensional block to the actual
Mathlib progression-free extremal function. All hypotheses after C are explicit
finite inequalities; they contain no assertion about Roth numbers. -/
theorem roth_finite_parameters (p m R N L J K : ℕ) [Fact p.Prime]
    (C : Certificate p) (hN : N ≤ p) (hL : 0 < L)
    (w : ℝ) (hw : 0 < w)
    (hwR : 2*w ≤ ((R:ℝ)/(p:ℝ))^2)
    (hwidth : (m:ℝ)*C.height < (L:ℝ)*w)
    (hD : N*((2*R+1)*(2*R+1))^m < (p*p)^m)
    (hJ : L*J ≤ C.block.card^m)
    (hK : (p*p)^m*K ≤ N*J) : K ≤ rothNumberNat N := by
  classical
  have hp : 0 < p := Nat.Prime.pos (Fact.out : p.Prime)
  let B : Finset (Fin m → ZMod p × ZMod p) := Fintype.piFinset fun _ => C.block
  let F : (Fin m → ZMod p × ZMod p) → ℝ := fun v => ∑ i, C.F (v i)
  have hB : B.card = C.block.card^m := Fintype.card_piFinset_const _ _
  have hF (v : Fin m → ZMod p × ZMod p) (hv : v ∈ B) :
      0 ≤ F v ∧ F v < (L:ℝ)*w := by
    have hm := Fintype.mem_piFinset.mp hv
    have bound (i : Fin m) := C.bounds (v i) (hm i)
    constructor
    · exact Finset.sum_nonneg (fun i _ => (bound i).1)
    · have upper : F v ≤ ∑ _i : Fin m, C.height :=
        Finset.sum_le_sum (fun i _ => (bound i).2)
      have upper' : F v ≤ (m:ℝ)*C.height := by simpa using upper
      exact upper'.trans_lt hwidth
  obtain ⟨S,hSB,hJS,b,hShell⟩ := exists_potential_shell B F w L J hw hL hF
    (by rw [hB];exact hJ)
  have hshort := shell_shortBox p m R hp C S
    (fun v hv i => Fintype.mem_piFinset.mp (hSB hv) i) b w hwR hShell
  have hcardG : Fintype.card (Fin m → ZMod p × ZMod p) = (p*p)^m := by
    simp [Fintype.card_prod,ZMod.card]
  apply roth_of_short_differences N K S (shortBox p m R) (fun d => slopePerm p m d)
  · exact fun d hd a => slopePerm_apply p m N d hN hd a
  · rw [hcardG]
    exact (Nat.mul_le_mul_left N (shortBox_card p m R)).trans_lt hD
  · exact hshort
  · rw [hcardG]
    exact hK.trans (Nat.mul_le_mul_left N hJS)

#print axioms shell_shortBox
#print axioms roth_finite_parameters

end
end Erdos142BlockCertificate
