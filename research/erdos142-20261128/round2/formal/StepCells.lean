import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace Erdos142BlockCertificate

structure Widths where
  L : ℕ → ℚ
  W : ℕ → ℚ
  P : ℕ → ℚ
  U : ℕ → ℚ
  V : ℕ → ℚ
  M : ℕ → ℚ

structure Valid (d K : ℕ) (T : Widths) : Prop where
  lower : ∀ i : Fin (2*d), 0 ≤ T.L i ∧ 0 ≤ T.W i ∧ T.L i+T.W i ≤ 1
  upper : ∀ j : Fin K, 0 ≤ T.P j ∧ T.P j ≤ 1 ∧ 0 ≤ T.U j ∧ T.U j ≤ 1 ∧
    0 ≤ T.V j ∧ T.V j ≤ 1 ∧ 0 ≤ T.M j ∧ T.M j ≤ 1
  angularV : ∀ j : Fin K, T.P j+T.U j+2*T.V j ≤ 2
  angularM : ∀ j : Fin K, T.P j+T.U j+2*T.M j ≤ 2
  ll : ∀ i j : Fin (2*d), ∀ b : Fin 2, let t := (i.val+j.val+b.val)/2
    t<K → T.L i+T.L j+T.P t ≤ 1 ∧ T.L i+T.L j+T.U t ≤ 1 ∧
      T.W i+T.W j+T.V t ≤ 1 ∧ T.W i+T.W j+T.M t ≤ 1
  lh : ∀ i : Fin (2*d), ∀ j : Fin K, ∀ b : Fin 2,
    let t := (i.val+j.val+2*d+b.val)/2
    t<K → T.P j+2*T.W i+2*T.V t ≤ 1 ∧ T.P j+2*T.W i+2*T.M t ≤ 1 ∧
      T.M j+2*T.L i+2*T.U t ≤ 1 ∧ T.M j+2*T.L i+2*T.P t ≤ 1

theorem valid_ll {d K : ℕ} {T : Widths} (h : Valid d K T)
    {i j t : ℕ} (hi : i<2*d) (hj : j<2*d) (ht : t<K)
    (indices : 2*t≤i+j+1 ∧ i+j≤2*t+1) :
    T.L i+T.L j+T.P t ≤ 1 ∧ T.L i+T.L j+T.U t ≤ 1 ∧
      T.W i+T.W j+T.V t ≤ 1 ∧ T.W i+T.W j+T.M t ≤ 1 := by
  have either : t=(i+j)/2 ∨ t=(i+j+1)/2 := by omega
  rcases either with rfl | rfl
  · simpa only [Nat.add_zero] using h.ll ⟨i,hi⟩ ⟨j,hj⟩ ⟨0,by decide⟩ ht
  · exact h.ll ⟨i,hi⟩ ⟨j,hj⟩ ⟨1,by decide⟩ ht

theorem valid_lh {d K : ℕ} {T : Widths} (h : Valid d K T)
    {i j t : ℕ} (hi : i<2*d) (hj : j<K) (ht : t<K)
    (indices : 2*t≤i+j+2*d+1 ∧ i+j+2*d≤2*t+1) :
    T.P j+2*T.W i+2*T.V t ≤ 1 ∧ T.P j+2*T.W i+2*T.M t ≤ 1 ∧
      T.M j+2*T.L i+2*T.U t ≤ 1 ∧ T.M j+2*T.L i+2*T.P t ≤ 1 := by
  have either : t=(i+j+2*d)/2 ∨ t=(i+j+2*d+1)/2 := by omega
  rcases either with rfl | rfl
  · simpa only [Nat.add_zero] using h.lh ⟨i,hi⟩ ⟨j,hj⟩ ⟨0,by decide⟩ ht
  · exact h.lh ⟨i,hi⟩ ⟨j,hj⟩ ⟨1,by decide⟩ ht

def Cell (D : ℕ) (g : ℝ) (i : ℕ) (s : ℝ) : Prop :=
  (i:ℝ)/(D:ℝ)+g/2 < s ∧ s < ((i:ℝ)+1)/(D:ℝ)-g/2

lemma cell_scaled {D i : ℕ} {g s : ℝ} (hD : 0<D) (hg : 0≤g)
    (h : Cell D g i s) : (i:ℝ) < s*(D:ℝ) ∧ s*(D:ℝ) < (i:ℝ)+1 := by
  have dp : 0<(D:ℝ) := by exact_mod_cast hD
  exact ⟨(div_lt_iff₀ dp).mp (by linarith only [h.1,hg]),
    (lt_div_iff₀ dp).mp (by linarith only [h.2,hg])⟩

lemma cell_bounds {D i : ℕ} {g s : ℝ} (hD : 0<D) (hg : 0≤g)
    (hi : i<D) (h : Cell D g i s) : 0<s ∧ s<1 := by
  have dp : 0<(D:ℝ) := by exact_mod_cast hD
  have ip : 0≤(i:ℝ) := by positivity
  have ih : (i:ℝ)+1≤(D:ℝ) := by exact_mod_cast (show i+1≤D by omega)
  have hs := cell_scaled hD hg h
  constructor <;> nlinarith only [dp,ip,ih,hs.1,hs.2]

lemma cell_low_half {d i : ℕ} {g s : ℝ} (hd : 0<d) (hg : 0≤g)
    (hi : i<2*d) (h : Cell (4*d) g i s) : s<1/2 := by
  have hs := (cell_scaled (by omega : 0<4*d) hg h).2
  have ih : (i:ℝ)+1≤2*(d:ℝ) := by exact_mod_cast (show i+1≤2*d by omega)
  have dp : 0<(d:ℝ) := by exact_mod_cast hd
  push_cast at hs
  nlinarith only [hs,ih,dp]

lemma cell_high_half {d j : ℕ} {g s : ℝ} (hd : 0<d) (hg : 0≤g)
    (h : Cell (4*d) g (2*d+j) s) : 1/2<s := by
  have hs := (cell_scaled (by omega : 0<4*d) hg h).1
  have jp : 0≤(j:ℝ) := by positivity
  have dp : 0<(d:ℝ) := by exact_mod_cast hd
  push_cast at hs
  nlinarith only [hs,jp,dp]

lemma cell_unique {D i j : ℕ} {g s : ℝ} (hD : 0<D) (hg : 0≤g)
    (hi : Cell D g i s) (hj : Cell D g j s) : i=j := by
  have bi := cell_scaled hD hg hi
  have bj := cell_scaled hD hg hj
  by_contra neq
  rcases lt_or_gt_of_ne neq with lt | gt
  · have h : (i:ℝ)+1≤(j:ℝ) := by exact_mod_cast (show i+1≤j by omega)
    linarith only [bi.2,bj.1,h]
  · have h : (j:ℝ)+1≤(i:ℝ) := by exact_mod_cast (show j+1≤i by omega)
    linarith only [bj.2,bi.1,h]

lemma cell_separated {D i j : ℕ} {g sx sz : ℝ} (hD : 0<D)
    (neq : i≠j) (hx : Cell D g i sx) (hz : Cell D g j sz) : g≤|sx-sz| := by
  have dp : 0<(D:ℝ) := by exact_mod_cast hD
  rcases lt_or_gt_of_ne neq with lt | gt
  · have h : (i:ℝ)+1≤(j:ℝ) := by exact_mod_cast (show i+1≤j by omega)
    have q := div_le_div_of_nonneg_right h dp.le
    have gap : g≤sz-sx := by linarith only [hx.2,hz.1,q]
    exact gap.trans (by simpa only [abs_sub_comm] using le_abs_self (sz-sx))
  · have h : (j:ℝ)+1≤(i:ℝ) := by exact_mod_cast (show j+1≤i by omega)
    have q := div_le_div_of_nonneg_right h dp.le
    have gap : g≤sx-sz := by linarith only [hz.2,hx.1,q]
    exact gap.trans (le_abs_self _)

lemma cell_midpoint {D i : ℕ} {g sx sy sz : ℝ}
    (hx : Cell D g i sx) (hz : Cell D g i sz) (hs : 2*sy=sx+sz) :
    Cell D g i sy := by
  constructor <;> linarith only [hx.1,hx.2,hz.1,hz.2,hs]

lemma cell_up_index {D i j t : ℕ} {g sx sy sz : ℝ} (hD : 0<D) (hg : 0≤g)
    (hx : Cell D g i sx) (hy : Cell D g t sy) (hz : Cell D g j sz)
    (hs : 2*sy=sx+sz+1) : 2*t≤i+j+D+1 ∧ i+j+D≤2*t+1 := by
  have bx := cell_scaled hD hg hx
  have by' := cell_scaled hD hg hy
  have bz := cell_scaled hD hg hz
  have eq := congrArg (fun x : ℝ => x*(D:ℝ)) hs
  have left : (2*t:ℕ)<i+j+D+2 := by
    have h : ((2*t:ℕ):ℝ)<((i+j+D+2:ℕ):ℝ) := by
      push_cast
      nlinarith only [eq,by'.1,bx.2,bz.2]
    exact_mod_cast h
  have right : i+j+D<2*t+2 := by
    have h : ((i+j+D:ℕ):ℝ)<((2*t+2:ℕ):ℝ) := by
      push_cast
      nlinarith only [eq,bx.1,bz.1,by'.2]
    exact_mod_cast h
  omega


#print axioms cell_up_index
#print axioms cell_separated

end Erdos142BlockCertificate
