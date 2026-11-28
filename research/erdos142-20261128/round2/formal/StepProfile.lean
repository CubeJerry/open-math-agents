import StepCells
import LayerGeometryCore
import SixWidthsAngular
import SixWidthsNoUp

namespace Erdos142BlockCertificate

def ProfileMem (d K : ℕ) (T : Widths) (g s a u : ℝ) : Prop :=
  (∃ i : Fin (2*d), Cell (4*d) g i s ∧ LowerArc (T.L i) (T.W i) a ∧ u=a) ∨
  (∃ j : Fin K, Cell (4*d) g (2*d+j) s ∧
    UpperLocal (T.P j) (T.U j) (T.V j) (T.M j) a u)

lemma valid_lower_real {d K : ℕ} {T : Widths} (h : Valid d K T) (i : Fin (2*d)) :
    0 ≤ (T.L i:ℝ) ∧ 0 ≤ (T.W i:ℝ) ∧ (T.L i:ℝ)+(T.W i:ℝ) ≤ 1 := by
  exact_mod_cast h.lower i

lemma valid_upper_real {d K : ℕ} {T : Widths} (h : Valid d K T) (j : Fin K) :
    0 ≤ (T.P j:ℝ) ∧ (T.P j:ℝ) ≤ 1 ∧ 0 ≤ (T.U j:ℝ) ∧ (T.U j:ℝ) ≤ 1 ∧
    0 ≤ (T.V j:ℝ) ∧ (T.V j:ℝ) ≤ 1 ∧ 0 ≤ (T.M j:ℝ) ∧ (T.M j:ℝ) ≤ 1 := by
  exact_mod_cast h.upper j

lemma valid_ll_real {d K : ℕ} {T : Widths} (h : Valid d K T)
    (i j : Fin (2*d)) (t : Fin K)
    (indices : 2*t.val≤i.val+j.val+1 ∧ i.val+j.val≤2*t.val+1) :
    (T.L i:ℝ)+(T.L j:ℝ)+(T.P t:ℝ) ≤ 1 ∧
    (T.L i:ℝ)+(T.L j:ℝ)+(T.U t:ℝ) ≤ 1 ∧
    (T.W i:ℝ)+(T.W j:ℝ)+(T.V t:ℝ) ≤ 1 ∧
    (T.W i:ℝ)+(T.W j:ℝ)+(T.M t:ℝ) ≤ 1 := by
  exact_mod_cast valid_ll h i.isLt j.isLt t.isLt indices

lemma valid_lh_real {d K : ℕ} {T : Widths} (h : Valid d K T)
    (i : Fin (2*d)) (j t : Fin K)
    (indices : 2*t.val≤i.val+j.val+2*d+1 ∧ i.val+j.val+2*d≤2*t.val+1) :
    (T.P j:ℝ)+2*(T.W i:ℝ)+2*(T.V t:ℝ) ≤ 1 ∧
    (T.P j:ℝ)+2*(T.W i:ℝ)+2*(T.M t:ℝ) ≤ 1 ∧
    (T.M j:ℝ)+2*(T.L i:ℝ)+2*(T.U t:ℝ) ≤ 1 ∧
    (T.M j:ℝ)+2*(T.L i:ℝ)+2*(T.P t:ℝ) ≤ 1 := by
  exact_mod_cast valid_lh h i.isLt j.isLt t.isLt indices

lemma upperLocal_arc {P U V M a u : ℝ} (h : UpperLocal P U V M a u) :
    UpperArc P U V M a := by
  rcases h with ⟨hl,hr,he⟩ | ⟨hl,hr,he⟩
  · left
    constructor <;> linarith only [hl,hr,he]
  · right
    constructor <;> linarith only [hl,hr,he]

lemma profile_bounds {d K : ℕ} {T : Widths} {g s a u : ℝ}
    (hd : 0<d) (hK : K≤2*d) (hg : 0≤g) (hT : Valid d K T)
    (h : ProfileMem d K T g s a u) :
    0<s ∧ s<1 ∧ |a|<1/2 ∧ |u|<1/2 := by
  have hD : 0<4*d := by omega
  rcases h with ⟨i,hs,ha,rfl⟩ | ⟨j,hs,ha⟩
  · have bs := cell_bounds hD hg (by have hi := i.isLt;omega) hs
    have hw := valid_lower_real hT i
    have aa : |u|<1/2 := by
      apply abs_lt.mpr
      constructor <;> linarith only [ha.1,ha.2,hw.1,hw.2.1,hw.2.2]
    exact ⟨bs.1,bs.2,aa,aa⟩
  · have bs := cell_bounds hD hg (by have hj := j.isLt;omega) hs
    obtain ⟨_,hP,_,hU,_,hV,_,hM⟩ := valid_upper_real hT j
    have ba := upper_local_bounds hP hU hV hM ha
    exact ⟨bs.1,bs.2,abs_lt.mpr ⟨ba.2.2.1,ba.2.2.2⟩,
      abs_lt.mpr ⟨ba.1,by linarith only [ba.2.1]⟩⟩

theorem profile_no_upward {d K : ℕ} {T : Widths} {g : ℝ}
    (hd : 0<d) (hK : K≤2*d) (hg : 0≤g) (hT : Valid d K T)
    {sx sy sz ax ay az ux uy uz : ℝ} {n : ℤ}
    (hx : ProfileMem d K T g sx ax ux)
    (hy : ProfileMem d K T g sy ay uy)
    (hz : ProfileMem d K T g sz az uz)
    (hs : 2*sy=sx+sz+1) (ha : ax+az-2*ay=(n:ℝ)) : False := by
  have hD : 0<4*d := by omega
  have bx := profile_bounds hd hK hg hT hx
  have bz := profile_bounds hd hK hg hT hz
  have by' := profile_bounds hd hK hg hT hy
  rcases hy with ⟨t,hys,_,_⟩ | ⟨t,hys,hya⟩
  · have syh := cell_low_half hd hg t.isLt hys
    linarith only [hs,syh,bx.1,bz.1]
  · rcases hx with ⟨i,hxs,hxa,_⟩ | ⟨i,hxs,hxa⟩ <;>
      rcases hz with ⟨j,hzs,hza,_⟩ | ⟨j,hzs,hza⟩
    · have indices := cell_up_index hD hg hxs hys hzs hs
      obtain ⟨hLP,hLU,hWV,hWM⟩ := valid_ll_real hT i j t (by omega)
      exact lower_lower_no_up hLP hLU hWV hWM hxa (upperLocal_arc hya) hza ha
    · have indices := cell_up_index hD hg hxs hys hzs hs
      obtain ⟨hPV,hPM,hMU,hMP⟩ := valid_lh_real hT i j t (by omega)
      obtain ⟨hP,_,_,hU,_,hV,hM,_⟩ := valid_upper_real hT j
      exact lower_upper_no_up hP hM hU hV hPV hPM hMU hMP
        hxa (upperLocal_arc hya) (upperLocal_arc hza) ha
    · have hss : 2*sy=sz+sx+1 := by linarith only [hs]
      have has : az+ax-2*ay=(n:ℝ) := by linarith only [ha]
      have indices := cell_up_index hD hg hzs hys hxs hss
      obtain ⟨hPV,hPM,hMU,hMP⟩ := valid_lh_real hT j i t (by omega)
      obtain ⟨hP,_,_,hU,_,hV,hM,_⟩ := valid_upper_real hT i
      exact lower_upper_no_up hP hM hU hV hPV hPM hMU hMP
        hza (upperLocal_arc hya) (upperLocal_arc hxa) has
    · have sxh := cell_high_half hd hg hxs
      have szh := cell_high_half hd hg hzs
      linarith only [hs,sxh,szh,by'.2.1]

lemma profile_at_lower_cell {d K i : ℕ} {T : Widths} {g s a u : ℝ}
    (hd : 0<d) (hg : 0≤g) (hi : i<2*d)
    (hc : Cell (4*d) g i s) (h : ProfileMem d K T g s a u) :
    LowerArc (T.L i) (T.W i) a ∧ u=a := by
  rcases h with ⟨j,hj,ha,hu⟩ | ⟨j,hj,_⟩
  · have eq := cell_unique (by omega : 0<4*d) hg hj hc
    simpa only [eq] using And.intro ha hu
  · have eq := cell_unique (by omega : 0<4*d) hg hj hc
    omega

lemma profile_at_upper_cell {d K j : ℕ} {T : Widths} {g s a u : ℝ}
    (hd : 0<d) (hg : 0≤g)
    (hc : Cell (4*d) g (2*d+j) s) (h : ProfileMem d K T g s a u) :
    UpperLocal (T.P j) (T.U j) (T.V j) (T.M j) a u := by
  rcases h with ⟨i,hi,_,_⟩ | ⟨i,hi,ha⟩
  · have eq := cell_unique (by omega : 0<4*d) hg hi hc
    have ilt := i.isLt
    omega
  · have eq := cell_unique (by omega : 0<4*d) hg hi hc
    have ij : i.val=j := by omega
    simpa only [ij] using ha

theorem profile_angular_or_separated {d K : ℕ} {T : Widths} {g : ℝ}
    (hd : 0<d) (hg : 0≤g) (hT : Valid d K T)
    {sx sy sz ax ay az ux uy uz : ℝ} {n : ℤ}
    (hx : ProfileMem d K T g sx ax ux)
    (hy : ProfileMem d K T g sy ay uy)
    (hz : ProfileMem d K T g sz az uz)
    (hs : 2*sy=sx+sz) (ha : ax+az-2*ay=(n:ℝ)) :
    (ax-az)^2 ≤ 4*(ux^2+uz^2-2*uy^2) ∨ g≤|sx-sz| := by
  have hD : 0<4*d := by omega
  rcases hx with ⟨i,hxs,hxa,hxu⟩ | ⟨i,hxs,hxa⟩ <;>
    rcases hz with ⟨j,hzs,hza,hzu⟩ | ⟨j,hzs,hza⟩
  · by_cases eq : i=j
    · subst j
      have hys := cell_midpoint hxs hzs hs
      obtain ⟨hya,hyu⟩ := profile_at_lower_cell hd hg i.isLt hys hy
      left
      rw [hxu,hzu,hyu]
      exact lower_width_jensen (valid_lower_real hT i).2.2 hxa hya hza ha
    · right
      exact cell_separated hD (by exact fun h => eq (Fin.ext h)) hxs hzs
  · right
    exact cell_separated hD (by have hi := i.isLt;omega) hxs hzs
  · right
    exact cell_separated hD (by have hj := j.isLt;omega) hxs hzs
  · by_cases eq : i=j
    · subst j
      have hys := cell_midpoint hxs hzs hs
      have hya := profile_at_upper_cell hd hg hys hy
      obtain ⟨_,hP,_,hU,_,hV,_,hM⟩ := valid_upper_real hT i
      have hA : (T.P i:ℝ)+(T.U i:ℝ)+2*(T.V i:ℝ)≤2 := by exact_mod_cast hT.angularV i
      have hB : (T.P i:ℝ)+(T.U i:ℝ)+2*(T.M i:ℝ)≤2 := by exact_mod_cast hT.angularM i
      exact Or.inl (upper_width_jensen hP hU hV hM hA hB hxa hya hza ha)
    · right
      apply cell_separated hD _ hxs hzs
      intro h
      exact eq (Fin.ext (by omega))

def profileGeometry {d K : ℕ} (T : Widths) (hT : Valid d K T)
    (hd : 0<d) (hK : K≤2*d) (g : ℝ) (hg : 0<g) (hg1 : g≤1) : Geometry where
  mem := ProfileMem d K T g
  separation := g
  separation_pos := hg
  separation_le_one := hg1
  bounds := profile_bounds hd hK hg.le hT
  no_upward := profile_no_upward hd hK hg.le hT
  angular_or_separated := profile_angular_or_separated hd hg.le hT

#print axioms profileGeometry
#print axioms profile_no_upward
#print axioms profile_angular_or_separated

end Erdos142BlockCertificate
