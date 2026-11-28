import LayerGeometry
import AsymptoticCertificate

/-! Finite-grid density for arbitrary verified rational cells. -/
namespace Erdos142BlockCertificate
open QuandleResearch.Erdos142
noncomputable section

structure CellFamily (G : Geometry) (D E : ℕ) (ι : Type*) where
  coords : ι → ℤ × ℤ
  injective : Function.Injective coords
  mem : ∀ i : ι, ∀ s a : ℝ,
    (coords i).1 / (D:ℝ) < s → s < ((coords i).1+1) / (D:ℝ) →
    (coords i).2 / (E:ℝ) < a → a < ((coords i).2+1) / (E:ℝ) →
    ∃ u, G.mem s a u

def gridBlock (G : Geometry) (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) := by
  classical
  exact Finset.univ.filter fun v => ∃ x y : ℤ, ∃ u : ℝ,
    (x : ZMod p)=v.1 ∧ (y : ZMod p)=v.2 ∧ G.mem (x/(p:ℝ)) (y/(p:ℝ)) u

def gridPoint {G : Geometry} {D E : ℕ} {ι : Type*}
    (C : CellFamily G D E ι) (p : ℕ) (i : ι) (t u : ℕ) : ℤ × ℤ :=
  (cellLift (C.coords i).1 ((p:ℝ)/D) t,
    cellLift (C.coords i).2 ((p:ℝ)/E) u)

lemma gridPoint_mem {G : Geometry} {D E : ℕ} {ι : Type*}
    (C : CellFamily G D E ι) (hD : 0<D) (hE : 0<E)
    (p : ℕ) (hp : 0<p) (i : ι) (t u : ℕ)
    (ht : (t+1)*D<p) (hu : (u+1)*E<p) :
    ∃ v, G.mem ((gridPoint C p i t u).1/(p:ℝ))
      ((gridPoint C p i t u).2/(p:ℝ)) v := by
  have hp' : (0:ℝ)<p := by exact_mod_cast hp
  have hD' : (0:ℝ)<D := by exact_mod_cast hD
  have hE' : (0:ℝ)<E := by exact_mod_cast hE
  have ht' : ((t:ℝ)+1)*D<(p:ℝ) := by exact_mod_cast ht
  have hu' : ((u:ℝ)+1)*E<(p:ℝ) := by exact_mod_cast hu
  have hs := normalized_cellLift_mem (i := (C.coords i).1) hp' hD' ht'
  have ha := normalized_cellLift_mem (i := (C.coords i).2) hp' hE' hu'
  exact C.mem i _ _ hs.1 hs.2 ha.1 ha.2

set_option maxRecDepth 8192 in
theorem gridBlock_card_lower {G : Geometry} {D E : ℕ} {ι : Type*} [Fintype ι]
    (C : CellFamily G D E ι) (hD : 0<D) (hE : 0<E)
    (p q r : ℕ) [NeZero p] (hq : q*D<p) (hr : r*E<p) :
    Fintype.card ι*q*r ≤ (gridBlock G p).card := by
  classical
  have hp : 0<p := NeZero.pos p
  have hp' : (0:ℝ)<p := by exact_mod_cast hp
  have hD' : (0:ℝ)<D := by exact_mod_cast hD
  have hE' : (0:ℝ)<E := by exact_mod_cast hE
  let f : ι × Fin q × Fin r → ZMod p × ZMod p := fun e =>
    ((gridPoint C p e.1 e.2.1.val e.2.2.val).1,
      (gridPoint C p e.1 e.2.1.val e.2.2.val).2)
  have hm (e : ι × Fin q × Fin r) :
      ∃ v, G.mem ((gridPoint C p e.1 e.2.1.val e.2.2.val).1/(p:ℝ))
        ((gridPoint C p e.1 e.2.1.val e.2.2.val).2/(p:ℝ)) v :=
    gridPoint_mem C hD hE p hp _ _ _
      (offset_mul_lt e.2.1.isLt hq) (offset_mul_lt e.2.2.isLt hr)
  have hf (e : ι × Fin q × Fin r) : f e ∈ gridBlock G p := by
    obtain ⟨v,hv⟩ := hm e
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,_,_,v,rfl,rfl,hv⟩
  have hinj : Function.Injective f := by
    rintro ⟨i,t,u⟩ ⟨j,t',u'⟩ he
    let x := gridPoint C p i t.val u.val
    let y := gridPoint C p j t'.val u'.val
    obtain ⟨vx,hx⟩ := hm (i,t,u)
    obtain ⟨vy,hy⟩ := hm (j,t',u')
    have bx := G.bounds hx
    have by' := G.bounds hy
    have hs := int_close_of_normalized_close hp (a := x.1) (b := y.1)
      (by linarith [bx.1,by'.2.1]) (by linarith [by'.1,bx.2.1])
    have hxs : x.1=y.1 := intCast_injective_close hs.1 hs.2 (congrArg Prod.fst he)
    obtain ⟨xl,xr⟩ := abs_lt.mp bx.2.2.1
    obtain ⟨yl,yr⟩ := abs_lt.mp by'.2.2.1
    have ha := int_close_of_normalized_close hp (a := x.2) (b := y.2)
      (by linarith) (by linarith)
    have hxa : x.2=y.2 := intCast_injective_close ha.1 ha.2 (congrArg Prod.snd he)
    have ht : (t.val:ℝ)+1<(p:ℝ)/D := by
      apply (lt_div_iff₀ hD').2
      exact_mod_cast (offset_mul_lt t.isLt hq)
    have ht' : (t'.val:ℝ)+1<(p:ℝ)/D := by
      apply (lt_div_iff₀ hD').2
      exact_mod_cast (offset_mul_lt t'.isLt hq)
    have hu : (u.val:ℝ)+1<(p:ℝ)/E := by
      apply (lt_div_iff₀ hE').2
      exact_mod_cast (offset_mul_lt u.isLt hr)
    have hu' : (u'.val:ℝ)+1<(p:ℝ)/E := by
      apply (lt_div_iff₀ hE').2
      exact_mod_cast (offset_mul_lt u'.isLt hr)
    have rows := cellLift_injective (by positivity : 0<(p:ℝ)/D) ht ht' hxs
    have cols := cellLift_injective (by positivity : 0<(p:ℝ)/E) hu hu' hxa
    have hij := C.injective (Prod.ext rows.1 cols.1)
    have htt : t=t' := Fin.ext rows.2
    have huu : u=u' := Fin.ext cols.2
    subst j;subst t';subst u';rfl
  let emb : ι × Fin q × Fin r → ↥(gridBlock G p) := fun e => ⟨f e,hf e⟩
  have hc := Fintype.card_le_of_injective emb
    (show Function.Injective emb from fun _ _ he => hinj (congrArg Subtype.val he))
  simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,Nat.mul_assoc] using hc

lemma scaled_div_lower (p d K : ℕ) (hd : 0<d) (hK : 0<K)
    (hpd : K*d≤p) :
    ((K:ℝ)-1)*p ≤ (K:ℝ)*d*(((p-1)/d:ℕ):ℝ) := by
  have hp : 0<p := lt_of_lt_of_le (Nat.mul_pos hK hd) hpd
  have hb := div_mul_bounds (p-1) d hd
  have hn : p ≤ (p-1)/d*d+d := by omega
  have hn' : (p:ℝ) ≤ (((p-1)/d:ℕ):ℝ)*d+d := by exact_mod_cast hn
  have hp' : (K:ℝ)*d≤p := by exact_mod_cast hpd
  have hm := mul_le_mul_of_nonneg_left hn' (Nat.cast_nonneg K : (0:ℝ)≤K)
  nlinarith only [hm,hp']

theorem gridBlock_density {G : Geometry} {D E : ℕ} {ι : Type*} [Fintype ι]
    (C : CellFamily G D E ι) (hD : 0<D) (hE : 0<E)
    (K : ℕ) (hK : 0<K) (ρ : ℝ)
    (harea : ρ*(K:ℝ)^2*D*E ≤ (Fintype.card ι:ℝ)*((K:ℝ)-1)^2)
    (p : ℕ) [NeZero p] (hpD : K*D≤p) (hpE : K*E≤p) :
    ρ*(p:ℝ)^2 ≤ ((gridBlock G p).card:ℝ) := by
  let q := (p-1)/D
  let r := (p-1)/E
  have hp : 0<p := NeZero.pos p
  have hq : q*D<p := by
    have hh := (div_mul_bounds (p-1) D hD).1
    dsimp [q];omega
  have hr : r*E<p := by
    have hh := (div_mul_bounds (p-1) E hE).1
    dsimp [r];omega
  have hc := gridBlock_card_lower C hD hE p q r hq hr
  have hc' : (Fintype.card ι:ℝ)*q*r ≤ ((gridBlock G p).card:ℝ) := by exact_mod_cast hc
  have loq := scaled_div_lower p D K hD hK hpD
  have lor := scaled_div_lower p E K hE hK hpE
  change ((K:ℝ)-1)*p ≤ (K:ℝ)*D*q at loq
  change ((K:ℝ)-1)*p ≤ (K:ℝ)*E*r at lor
  have hK' : (1:ℝ)≤K := by exact_mod_cast (show 1≤K by omega)
  have prod := mul_le_mul loq lor
    (show (0:ℝ)≤((K:ℝ)-1)*p by positivity)
    (show (0:ℝ)≤(K:ℝ)*D*q by positivity)
  have positive : (0:ℝ)<(K:ℝ)^2*D*E := by
    have : (0:ℝ)<D := by exact_mod_cast hD
    have : (0:ℝ)<E := by exact_mod_cast hE
    have : (0:ℝ)<K := by exact_mod_cast hK
    positivity
  apply le_of_mul_le_mul_right (a := (K:ℝ)^2*D*E) _ positive
  calc
    (ρ*(p:ℝ)^2)*((K:ℝ)^2*D*E) ≤
        (Fintype.card ι:ℝ)*((K:ℝ)-1)^2*(p:ℝ)^2 := by
      have scaled := mul_le_mul_of_nonneg_right harea (sq_nonneg (p:ℝ))
      linarith only [scaled]
    _ ≤ (Fintype.card ι:ℝ)*((K:ℝ)*D*q)*((K:ℝ)*E*r) := by
      have scaled := mul_le_mul_of_nonneg_left prod
        (Nat.cast_nonneg (Fintype.card ι) : (0:ℝ)≤Fintype.card ι)
      linarith only [scaled]
    _ = ((Fintype.card ι:ℝ)*q*r)*((K:ℝ)^2*D*E) := by ring
    _ ≤ ((gridBlock G p).card:ℝ)*((K:ℝ)^2*D*E) :=
      mul_le_mul_of_nonneg_right hc' positive.le

theorem gridBlock_lifts (G : Geometry) (p : ℕ) [NeZero p] :
    ∃ X Y : ZMod p × ZMod p → ℤ, ∃ U : ZMod p × ZMod p → ℝ,
      ∀ v ∈ gridBlock G p,
        (X v:ZMod p)=v.1 ∧ (Y v:ZMod p)=v.2 ∧
          G.mem ((X v:ℝ)/p) ((Y v:ℝ)/p) (U v) := by
  classical
  have h (v : ZMod p × ZMod p) : ∃ x y : ℤ, ∃ u : ℝ,
      v ∈ gridBlock G p → (x:ZMod p)=v.1 ∧ (y:ZMod p)=v.2 ∧
        G.mem (x/(p:ℝ)) (y/(p:ℝ)) u := by
    by_cases hv : v ∈ gridBlock G p
    · obtain ⟨x,y,u,hx,hy,hm⟩ := (Finset.mem_filter.mp hv).2
      exact ⟨x,y,u,fun _ => ⟨hx,hy,hm⟩⟩
    · exact ⟨0,0,0,fun he => (hv he).elim⟩
  choose X Y U hXYU using h
  exact ⟨X,Y,U,hXYU⟩

theorem uniformDensity_of_cells {G : Geometry} {D E : ℕ} {ι : Type*} [Fintype ι]
    (C : CellFamily G D E ι) (hD : 0<D) (hE : 0<E)
    (K : ℕ) (hK : 0<K) (ρ M : ℝ) (H : ℕ)
    (harea : ρ*(K:ℝ)^2*D*E ≤ (Fintype.card ι:ℝ)*((K:ℝ)-1)^2)
    (hM : 2≤M) (hpay : 6≤(M-2)*G.separation^2) (hH : M+1≤(H:ℝ)) :
    UniformDensity ρ H (K*max D E) := by
  intro p hp hlarge
  let _ : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨X,Y,U,hl⟩ := gridBlock_lifts G p
  let B := certificateOfGeometry p hp.pos G M hM hpay (gridBlock G p) X Y U
    (fun v hv => ⟨(hl v hv).1,(hl v hv).2.1⟩) (fun v hv => (hl v hv).2.2)
  refine ⟨B,hH,?_⟩
  exact gridBlock_density C hD hE K hK ρ harea p
    ((Nat.mul_le_mul_left K (le_max_left D E)).trans hlarge)
    ((Nat.mul_le_mul_left K (le_max_right D E)).trans hlarge)

#print axioms gridBlock_card_lower
#print axioms gridBlock_density
#print axioms uniformDensity_of_cells
end
end Erdos142BlockCertificate
