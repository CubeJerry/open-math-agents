import StepProfile
import SixWidths192Numerators

namespace Erdos142BlockCertificate.SixWidths192

def widths192 : Widths where
  L i := (Lnum i:ℚ)/4480
  W i := (Wnum i:ℚ)/4480
  P j := (Pnum j:ℚ)/4480
  U j := (Unum j:ℚ)/4480
  V j := (Vnum j:ℚ)/4480
  M j := (Mnum j:ℚ)/4480

theorem valid192 : Valid 48 80 widths192 := by
  constructor
  · intro i
    have hw : (Lnum i:ℚ)+(Wnum i:ℚ)≤4480 := by
      exact_mod_cast lower_numerators i i.isLt
    dsimp only [widths192]
    refine ⟨by positivity,by positivity,?_⟩
    linarith only [hw]
  · intro j
    have h : (Pnum j:ℚ)≤4480 ∧ (Unum j:ℚ)≤4480 ∧
        (Vnum j:ℚ)≤4480 ∧ (Mnum j:ℚ)≤4480 := by
      exact_mod_cast upper_numerators j j.isLt
    rcases h with ⟨hP,hU,hV,hM⟩
    dsimp only [widths192]
    refine ⟨by positivity,?_,by positivity,?_,by positivity,?_,by positivity,?_⟩ <;>
      linarith only [hP,hU,hV,hM]
  · intro j
    have h : (Pnum j:ℚ)+(Unum j:ℚ)+2*(Vnum j:ℚ)≤8960 := by
      exact_mod_cast (angular_numerators j j.isLt).1
    dsimp only [widths192]
    linarith only [h]
  · intro j
    have h : (Pnum j:ℚ)+(Unum j:ℚ)+2*(Mnum j:ℚ)≤8960 := by
      exact_mod_cast (angular_numerators j j.isLt).2
    dsimp only [widths192]
    linarith only [h]
  · intro i j b t ht
    have hi : i.val+j.val≤2*t+1 := by
      dsimp [t]
      have hb := b.isLt
      omega
    have h : (Lnum i:ℚ)+(Lnum j:ℚ)+(Pnum t:ℚ)≤4480 ∧
        (Lnum i:ℚ)+(Lnum j:ℚ)+(Unum t:ℚ)≤4480 ∧
        (Wnum i:ℚ)+(Wnum j:ℚ)+(Vnum t:ℚ)≤4480 ∧
        (Wnum i:ℚ)+(Wnum j:ℚ)+(Mnum t:ℚ)≤4480 := by
      exact_mod_cast ll_numerators i j t ht hi
    rcases h with ⟨hP,hU,hV,hM⟩
    change (Lnum i:ℚ)/4480+(Lnum j:ℚ)/4480+(Pnum t:ℚ)/4480≤1 ∧
      (Lnum i:ℚ)/4480+(Lnum j:ℚ)/4480+(Unum t:ℚ)/4480≤1 ∧
      (Wnum i:ℚ)/4480+(Wnum j:ℚ)/4480+(Vnum t:ℚ)/4480≤1 ∧
      (Wnum i:ℚ)/4480+(Wnum j:ℚ)/4480+(Mnum t:ℚ)/4480≤1
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hP,hU,hV,hM]
  · intro i j b t ht
    have hi : i.val+j.val+96≤2*t+1 := by
      dsimp [t]
      have hb := b.isLt
      omega
    have h : (Pnum j:ℚ)+2*(Wnum i:ℚ)+2*(Vnum t:ℚ)≤4480 ∧
        (Pnum j:ℚ)+2*(Wnum i:ℚ)+2*(Mnum t:ℚ)≤4480 ∧
        (Mnum j:ℚ)+2*(Lnum i:ℚ)+2*(Unum t:ℚ)≤4480 ∧
        (Mnum j:ℚ)+2*(Lnum i:ℚ)+2*(Pnum t:ℚ)≤4480 := by
      exact_mod_cast lh_numerators i j t ht hi
    rcases h with ⟨hV,hM,hU,hP⟩
    change (Pnum j:ℚ)/4480+2*((Wnum i:ℚ)/4480)+2*((Vnum t:ℚ)/4480)≤1 ∧
      (Pnum j:ℚ)/4480+2*((Wnum i:ℚ)/4480)+2*((Mnum t:ℚ)/4480)≤1 ∧
      (Mnum j:ℚ)/4480+2*((Lnum i:ℚ)/4480)+2*((Unum t:ℚ)/4480)≤1 ∧
      (Mnum j:ℚ)/4480+2*((Lnum i:ℚ)/4480)+2*((Pnum t:ℚ)/4480)≤1
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hV,hM,hU,hP]

noncomputable def geometry192 : Geometry :=
  profileGeometry widths192 valid192 (by decide) (by decide)
    (1/1000000) (by norm_num) (by norm_num)

@[simp] theorem geometry192_separation : geometry192.separation=(1/1000000:ℝ) := rfl

def potentialCoeff : ℕ := 6000000000002

theorem potentialCoeff_ge_two : 2≤(potentialCoeff:ℝ) := by norm_num [potentialCoeff]

theorem potentialCoeff_pays : 6≤((potentialCoeff:ℝ)-2)*geometry192.separation^2 := by
  norm_num [potentialCoeff]

theorem lower_rectangle_mem (i : Fin 96) {s a : ℝ}
    (hs : Cell 192 (1/1000000) i s)
    (ha : -(2*(Lnum i:ℝ))/17920<a ∧ a<(2*(Wnum i:ℝ))/17920) :
    geometry192.mem s a a := by
  change ProfileMem 48 80 widths192 (1/1000000) s a a
  refine Or.inl ⟨i,hs,?_,rfl⟩
  change -(((Lnum i:ℚ)/4480:ℚ):ℝ)/2<a ∧ a<(((Wnum i:ℚ)/4480:ℚ):ℝ)/2
  push_cast
  constructor <;> linarith only [ha.1,ha.2]

theorem positive_rectangle_mem (j : Fin 80) {s a : ℝ}
    (hs : Cell 192 (1/1000000) (96+j) s)
    (ha : (4480-(Vnum j:ℝ))/17920<a ∧ a<(4480+(Pnum j:ℝ))/17920) :
    geometry192.mem s a (a-1/2) := by
  change ProfileMem 48 80 widths192 (1/1000000) s a (a-1/2)
  refine Or.inr ⟨j,hs,Or.inl ?_⟩
  dsimp only [widths192]
  push_cast
  refine ⟨?_,?_,?_⟩ <;> linarith only [ha.1,ha.2]

theorem negative_rectangle_mem (j : Fin 80) {s a : ℝ}
    (hs : Cell 192 (1/1000000) (96+j) s)
    (ha : (-4480-(Mnum j:ℝ))/17920<a ∧ a<(-4480+(Unum j:ℝ))/17920) :
    geometry192.mem s a a := by
  change ProfileMem 48 80 widths192 (1/1000000) s a a
  refine Or.inr ⟨j,hs,Or.inr ?_⟩
  dsimp only [widths192]
  push_cast
  refine ⟨?_,?_,rfl⟩ <;> linarith only [ha.1,ha.2]

#print axioms valid192
#print axioms geometry192
#print axioms potentialCoeff_pays
#print axioms lower_rectangle_mem
#print axioms positive_rectangle_mem
#print axioms negative_rectangle_mem

end Erdos142BlockCertificate.SixWidths192
