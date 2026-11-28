import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Finset.Range
import Lean.Elab.Tactic.Omega

/-!
Exact integer numerators for the D=192 step infima of the six-width profile
with parameters p=6/5, q=9/10 and w=17/140. All widths have denominator 4480.
The finite feasibility certificate below is symbolic: it does not enumerate
the endpoint-pair constraints.
-/

namespace Erdos142BlockCertificate.SixWidths192

def Lnum (i : ℕ) : ℕ := 28*i
def Wnum (i : ℕ) : ℕ := min (544+21*i) (4452-28*i)
def Unum (j : ℕ) : ℕ := 4424-56*j
def Pnum (j : ℕ) : ℕ := min (Unum j) (640+42*j)
def Vnum (j : ℕ) : ℕ := min (1920+7*j) (3350-42*j)
def Mnum (j : ℕ) : ℕ := min (Vnum j) (896+56*j)

theorem lower_numerators (i : ℕ) (hi : i<96) : Lnum i+Wnum i≤4480 := by
  have wh : Wnum i≤4452-28*i := min_le_right _ _
  dsimp [Lnum]
  omega

theorem upper_numerators (j : ℕ) (hj : j<80) :
    Pnum j≤4480 ∧ Unum j≤4480 ∧ Vnum j≤4480 ∧ Mnum j≤4480 := by
  have u1 : Unum j≤4480 := by dsimp [Unum];omega
  have p1 : Pnum j≤4480 := (min_le_left _ _).trans u1
  have v1 : Vnum j≤4480 := (min_le_left _ _).trans (by omega)
  have m1 : Mnum j≤4480 := (min_le_left _ _).trans v1
  exact ⟨p1,u1,v1,m1⟩

theorem angular_numerators (j : ℕ) (hj : j<80) :
    Pnum j+Unum j+2*Vnum j≤8960 ∧ Pnum j+Unum j+2*Mnum j≤8960 := by
  have ph : Pnum j≤640+42*j := min_le_right _ _
  have vh : Vnum j≤1920+7*j := min_le_left _ _
  have mh : Mnum j≤Vnum j := min_le_left _ _
  dsimp [Unum]
  omega

theorem ll_numerators (i j t : ℕ) (ht : t<80) (h : i+j≤2*t+1) :
    Lnum i+Lnum j+Pnum t≤4480 ∧ Lnum i+Lnum j+Unum t≤4480 ∧
    Wnum i+Wnum j+Vnum t≤4480 ∧ Wnum i+Wnum j+Mnum t≤4480 := by
  have ph : Pnum t≤Unum t := min_le_left _ _
  have whi : Wnum i≤544+21*i := min_le_left _ _
  have whj : Wnum j≤544+21*j := min_le_left _ _
  have vh : Vnum t≤3350-42*t := min_le_right _ _
  have mh : Mnum t≤Vnum t := min_le_left _ _
  dsimp [Lnum,Unum] at *
  omega

theorem lh_numerators (i j t : ℕ) (ht : t<80) (h : i+j+96≤2*t+1) :
    Pnum j+2*Wnum i+2*Vnum t≤4480 ∧ Pnum j+2*Wnum i+2*Mnum t≤4480 ∧
    Mnum j+2*Lnum i+2*Unum t≤4480 ∧ Mnum j+2*Lnum i+2*Pnum t≤4480 := by
  have phj : Pnum j≤640+42*j := min_le_right _ _
  have whi : Wnum i≤544+21*i := min_le_left _ _
  have vht : Vnum t≤3350-42*t := min_le_right _ _
  have mht : Mnum t≤Vnum t := min_le_left _ _
  have mhj : Mnum j≤896+56*j := min_le_right _ _
  have pht : Pnum t≤Unum t := min_le_left _ _
  dsimp [Lnum,Unum] at *
  omega

def totalColumns : ℕ :=
  (∑ i ∈ Finset.range 96, 2*(Lnum i+Wnum i))+
    (∑ j ∈ Finset.range 80, (Pnum j+Unum j+Vnum j+Mnum j))

set_option maxRecDepth 10000 in
theorem totalColumns_eq : totalColumns=1034322 := by decide

#print axioms lower_numerators
#print axioms upper_numerators
#print axioms angular_numerators
#print axioms ll_numerators
#print axioms lh_numerators
#print axioms totalColumns_eq

end Erdos142BlockCertificate.SixWidths192
