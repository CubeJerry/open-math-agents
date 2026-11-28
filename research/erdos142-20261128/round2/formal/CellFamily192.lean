import GridDensity
import SixWidths192

namespace Erdos142BlockCertificate.SixWidths192
noncomputable section

abbrev LowerIndex := Σ i : Fin 96, Fin 31244 × Fin (2*(Lnum i+Wnum i))
abbrev PositiveIndex := Σ j : Fin 80, Fin 31244 × Fin (Vnum j+Pnum j)
abbrev NegativeIndex := Σ j : Fin 80, Fin 31244 × Fin (Mnum j+Unum j)
abbrev CellIndex := LowerIndex ⊕ PositiveIndex ⊕ NegativeIndex

def cellCoords : CellIndex → ℤ × ℤ
  | Sum.inl ⟨i,t,k⟩ => ((i.val:ℤ)*31250+3+t.val, -2*(Lnum i:ℤ)+k.val)
  | Sum.inr (Sum.inl ⟨j,t,k⟩) =>
      (((j.val:ℤ)+96)*31250+3+t.val,4480-(Vnum j:ℤ)+k.val)
  | Sum.inr (Sum.inr ⟨j,t,k⟩) =>
      (((j.val:ℤ)+96)*31250+3+t.val,-4480-(Mnum j:ℤ)+k.val)

theorem cellCoords_injective : Function.Injective cellCoords := by
  intro e f he
  rcases e with ⟨i,t,k⟩ | ⟨i,t,k⟩ | ⟨i,t,k⟩ <;>
    rcases f with ⟨i',t',k'⟩ | ⟨i',t',k'⟩ | ⟨i',t',k'⟩
  all_goals
    have hr := congrArg Prod.fst he
    have hc := congrArg Prod.snd he
    dsimp only [cellCoords] at hr hc
    have hi := i.isLt
    have hi' := i'.isLt
    have ht := t.isLt
    have ht' := t'.isLt
    have hk := k.isLt
    have hk' := k'.isLt
  · have ii : i=i' := Fin.ext (by omega)
    subst i'
    have tt : t=t' := Fin.ext (by omega)
    subst t'
    have kk : k=k' := Fin.ext (by omega)
    subst k';rfl
  · omega
  · omega
  · omega
  · have ii : i=i' := Fin.ext (by omega)
    subst i'
    have tt : t=t' := Fin.ext (by omega)
    subst t'
    have kk : k=k' := Fin.ext (by omega)
    subst k';rfl
  · have hv := (upper_numerators i hi).2.2.1
    have hu := (upper_numerators i' hi').2.1
    omega
  · omega
  · have hu := (upper_numerators i hi).2.1
    have hv := (upper_numerators i' hi').2.2.1
    omega
  · have ii : i=i' := Fin.ext (by omega)
    subst i'
    have tt : t=t' := Fin.ext (by omega)
    subst t'
    have kk : k=k' := Fin.ext (by omega)
    subst k';rfl

lemma microcell_height (i : ℕ) (t : Fin 31244) {s : ℝ}
    (hs₁ : ((i:ℝ)*31250+3+t.val)/6000000<s)
    (hs₂ : s<((i:ℝ)*31250+3+t.val+1)/6000000) :
    Cell 192 (1/1000000) i s := by
  have ht : (t.val:ℝ)+1≤31244 := by exact_mod_cast (show t.val+1≤31244 by have := t.isLt;omega)
  have ht0 : (0:ℝ)≤t.val := by positivity
  constructor <;> linarith only [hs₁,hs₂,ht,ht0]

theorem cells_mem (e : CellIndex) (s a : ℝ)
    (hs₁ : (cellCoords e).1/(6000000:ℝ)<s)
    (hs₂ : s<((cellCoords e).1+1)/(6000000:ℝ))
    (ha₁ : (cellCoords e).2/(17920:ℝ)<a)
    (ha₂ : a<((cellCoords e).2+1)/(17920:ℝ)) :
    ∃ u, geometry192.mem s a u := by
  rcases e with ⟨i,t,k⟩ | ⟨j,t,k⟩ | ⟨j,t,k⟩
  · dsimp only [cellCoords] at hs₁ hs₂ ha₁ ha₂
    push_cast at hs₁ hs₂ ha₁ ha₂
    have hs := microcell_height i t hs₁ hs₂
    have hk : (k.val:ℝ)+1≤2*((Lnum i:ℝ)+(Wnum i:ℝ)) := by
      exact_mod_cast (show k.val+1≤2*(Lnum i+Wnum i) by have := k.isLt;omega)
    have hk0 : (0:ℝ)≤k.val := by positivity
    refine ⟨a,lower_rectangle_mem i hs ?_⟩
    constructor <;> linarith only [ha₁,ha₂,hk,hk0]
  · dsimp only [cellCoords] at hs₁ hs₂ ha₁ ha₂
    push_cast at hs₁ hs₂ ha₁ ha₂
    have hs : Cell 192 (1/1000000) (96+j) s := by
      apply microcell_height (96+j) t
      · push_cast;linarith only [hs₁]
      · push_cast;linarith only [hs₂]
    have hk : (k.val:ℝ)+1≤(Vnum j:ℝ)+(Pnum j:ℝ) := by
      exact_mod_cast (show k.val+1≤Vnum j+Pnum j by have := k.isLt;omega)
    have hk0 : (0:ℝ)≤k.val := by positivity
    refine ⟨a-1/2,positive_rectangle_mem j hs ?_⟩
    constructor <;> linarith only [ha₁,ha₂,hk,hk0]
  · dsimp only [cellCoords] at hs₁ hs₂ ha₁ ha₂
    push_cast at hs₁ hs₂ ha₁ ha₂
    have hs : Cell 192 (1/1000000) (96+j) s := by
      apply microcell_height (96+j) t
      · push_cast;linarith only [hs₁]
      · push_cast;linarith only [hs₂]
    have hk : (k.val:ℝ)+1≤(Mnum j:ℝ)+(Unum j:ℝ) := by
      exact_mod_cast (show k.val+1≤Mnum j+Unum j by have := k.isLt;omega)
    have hk0 : (0:ℝ)≤k.val := by positivity
    refine ⟨a,negative_rectangle_mem j hs ?_⟩
    constructor <;> linarith only [ha₁,ha₂,hk,hk0]

def cells192 : CellFamily geometry192 6000000 17920 CellIndex where
  coords := cellCoords
  injective := cellCoords_injective
  mem := cells_mem

theorem cellIndex_card : Fintype.card CellIndex=31244*1034322 := by
  classical
  have h : Fintype.card CellIndex=31244*totalColumns := by
    simp only [CellIndex,LowerIndex,PositiveIndex,NegativeIndex,Fintype.card_sum,
      Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
    simp only [totalColumns,Finset.sum_range,Finset.mul_sum,Finset.sum_add_distrib,mul_add]
    ring
  rw [h,totalColumns_eq]

theorem density_three_tenths : UniformDensity (3/10) 6000000000003 60000000000 := by
  apply uniformDensity_of_cells cells192 (by decide) (by decide)
    10000 (by decide) (3/10) (potentialCoeff:ℝ) 6000000000003
  · rw [cellIndex_card]
    norm_num
  · exact potentialCoeff_ge_two
  · exact potentialCoeff_pays
  · norm_num [potentialCoeff]

#print axioms cells192
#print axioms cellIndex_card
#print axioms density_three_tenths
end
end Erdos142BlockCertificate.SixWidths192
