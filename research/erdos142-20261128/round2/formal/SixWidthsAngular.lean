import IntegerWraps

/-! Angular Jensen certificate for a constant six-width height layer. -/
namespace Erdos142BlockCertificate


def UpperLocal (P U V M a u : ℝ) : Prop :=
  (-(1+V)/4 < u ∧ u < (P-1)/4 ∧ a=u+1/2) ∨
  (-(1+M)/4 < u ∧ u < (U-1)/4 ∧ a=u)

lemma upper_local_bounds {P U V M a u : ℝ}
    (hP : P ≤ 1) (hU : U ≤ 1) (hV : V ≤ 1) (hM : M ≤ 1)
    (h : UpperLocal P U V M a u) :
    -(1/2:ℝ) < u ∧ u < 0 ∧ -(1/2:ℝ) < a ∧ a < 1/2 := by
  rcases h with ⟨hl,hr,he⟩ | ⟨hl,hr,he⟩ <;> constructor <;> try linarith
  all_goals constructor <;> try linarith
  all_goals constructor <;> linarith

lemma upper_local_rep {P U V M a u : ℝ} (h : UpperLocal P U V M a u) :
    ∃ i : ℤ, 0 ≤ i ∧ i ≤ 1 ∧ a=u+(i:ℝ)/2 := by
  rcases h with ⟨_,_,he⟩ | ⟨_,_,he⟩
  · exact ⟨1,by omega,by omega,by simpa using he⟩
  · exact ⟨0,by omega,by omega,by simpa using he⟩

lemma same_label_jensen {ax ay az ux uy uz : ℝ} {i iy j : ℤ}
    (hxl : -(1/2:ℝ)<ux) (hxr : ux<0)
    (hyl : -(1/2:ℝ)<uy) (hyr : uy<0)
    (hzl : -(1/2:ℝ)<uz) (hzr : uz<0)
    (hx : ax=ux+(i:ℝ)/2) (hy : ay=uy+(iy:ℝ)/2) (hz : az=uz+(i:ℝ)/2)
    (ha : ax+az-2*ay=(j:ℝ)) :
    (ax-az)^2 ≤ 4*(ux^2+uz^2-2*uy^2) := by
  have eq : ((j-i+iy:ℤ):ℝ)=ux+uz-2*uy := by push_cast;linarith
  have zero := int_zero_of_unit_bounds (j-i+iy)
    (by rw [eq];linarith) (by rw [eq];linarith)
  have z : ((j-i+iy:ℤ):ℝ)=0 := by exact_mod_cast zero
  have mean : uy=(ux+uz)/2 := by linarith
  rw [mean,hx,hz]
  nlinarith only [sq_nonneg (ux-uz)]

lemma cross_label_jensen {P U V M ax ay az ux uy uz : ℝ} {j : ℤ}
    (hP : P ≤ 1) (hU : U ≤ 1) (hV : V ≤ 1) (hM : M ≤ 1)
    (hA : P+U+2*V ≤ 2) (hB : P+U+2*M ≤ 2)
    (hx : -(1+V)/4 < ux ∧ ux < (P-1)/4 ∧ ax=ux+1/2)
    (hy : UpperLocal P U V M ay uy)
    (hz : -(1+M)/4 < uz ∧ uz < (U-1)/4 ∧ az=uz)
    (ha : ax+az-2*ay=(j:ℝ)) :
    (ax-az)^2 ≤ 4*(ux^2+uz^2-2*uy^2) := by
  have bx := upper_local_bounds hP hU hV hM (Or.inl hx)
  have by' := upper_local_bounds hP hU hV hM hy
  have bz := upper_local_bounds hP hU hV hM (Or.inr hz)
  have cap : ux+uz-2*uy < 1/2 := by
    rcases hy with ⟨hl,_,_⟩ | ⟨hl,_,_⟩ <;> linarith [hx.2.1,hz.2.1]
  obtain ⟨iy,_,_,hiy⟩ := upper_local_rep hy
  have eq : ((j+iy:ℤ):ℝ)=ux+uz-2*uy+1/2 := by
    push_cast
    linarith [hx.2.2,hz.2.2]
  have zero := int_zero_of_unit_bounds (j+iy)
    (by rw [eq];linarith [bx.1,bz.1,by'.2.1]) (by rw [eq];linarith)
  have z : ((j+iy:ℤ):ℝ)=0 := by exact_mod_cast zero
  have mean : uy=(ux+uz)/2+1/4 := by linarith
  have sum : ux+uz ≤ -(1/2:ℝ) := by linarith [by'.2.1]
  have Q : (ux-uz)^2/2+1/8 ≤ ux^2+uz^2-2*uy^2 := by
    rw [mean]
    nlinarith only [sum]
  have distance : (ax-az)^2 ≤ 2*(ux-uz)^2+1/2 := by
    rw [hx.2.2,hz.2.2]
    nlinarith only [sq_nonneg (ux-uz-1/2)]
  nlinarith only [Q,distance]

/-- The two within-layer LP inequalities permit the downward folded angular
midpoint; that case supplies additional Jensen curvature. -/
theorem upper_width_jensen {P U V M ax ay az ux uy uz : ℝ} {j : ℤ}
    (hP : P ≤ 1) (hU : U ≤ 1) (hV : V ≤ 1) (hM : M ≤ 1)
    (hA : P+U+2*V ≤ 2) (hB : P+U+2*M ≤ 2)
    (hx : UpperLocal P U V M ax ux) (hy : UpperLocal P U V M ay uy)
    (hz : UpperLocal P U V M az uz) (ha : ax+az-2*ay=(j:ℝ)) :
    (ax-az)^2 ≤ 4*(ux^2+uz^2-2*uy^2) := by
  have bx := upper_local_bounds hP hU hV hM hx
  have by' := upper_local_bounds hP hU hV hM hy
  have bz := upper_local_bounds hP hU hV hM hz
  obtain ⟨iy,_,_,hiy⟩ := upper_local_rep hy
  rcases hx with hx | hx <;> rcases hz with hz | hz
  · exact same_label_jensen bx.1 bx.2.1 by'.1 by'.2.1 bz.1 bz.2.1
      (i := 1) (by simpa using hx.2.2) hiy (by simpa using hz.2.2) ha
  · exact cross_label_jensen hP hU hV hM hA hB hx hy hz ha
  · have h := cross_label_jensen hP hU hV hM hA hB hz hy hx (by linarith : az+ax-2*ay=(j:ℝ))
    nlinarith only [h]
  · exact same_label_jensen bx.1 bx.2.1 by'.1 by'.2.1 bz.1 bz.2.1
      (i := 0) (by simpa using hx.2.2) hiy (by simpa using hz.2.2) ha

theorem lower_width_jensen {L W ax ay az : ℝ} {j : ℤ}
    (hwidth : L+W ≤ 1)
    (hx : -L/2 < ax ∧ ax < W/2)
    (hy : -L/2 < ay ∧ ay < W/2)
    (hz : -L/2 < az ∧ az < W/2)
    (ha : ax+az-2*ay=(j:ℝ)) :
    (ax-az)^2 ≤ 4*(ax^2+az^2-2*ay^2) := by
  have zero := int_zero_of_unit_bounds j (by linarith [hx.1,hz.1,hy.2])
    (by linarith [hx.2,hz.2,hy.1])
  subst j
  norm_num at ha
  have mean : ay=(ax+az)/2 := by linarith
  rw [mean]
  nlinarith only [sq_nonneg (ax-az)]

#print axioms upper_width_jensen
#print axioms lower_width_jensen

end Erdos142BlockCertificate
