import IntegerWraps

/-! Exact angular exclusion lemmas for the six-width LP constraints. -/
namespace Erdos142BlockCertificate


def LowerArc (L W a : ℝ) : Prop := -L/2 < a ∧ a < W/2

def UpperArc (P U V M a : ℝ) : Prop :=
  (1/4-V/4 < a ∧ a < 1/4+P/4) ∨
  (-1/4-M/4 < a ∧ a < -1/4+U/4)

/-- The four LL inequalities exclude every integer horizontal wrap. -/
theorem lower_lower_no_up {Lx Wx Lz Wz P U V M ax ay az : ℝ} {j : ℤ}
    (hLP : Lx+Lz+P ≤ 1) (hLU : Lx+Lz+U ≤ 1)
    (hWV : Wx+Wz+V ≤ 1) (hWM : Wx+Wz+M ≤ 1)
    (hx : LowerArc Lx Wx ax) (hy : UpperArc P U V M ay)
    (hz : LowerArc Lz Wz az) (ha : ax+az-2*ay=(j:ℝ)) : False := by
  rcases hy with ⟨yl,yr⟩ | ⟨yl,yr⟩
  · exact no_int_neg_one_zero j (by linarith only [hx.1,hz.1,yr,hLP,ha])
      (by linarith only [hx.2,hz.2,yl,hWV,ha])
  · exact no_int_zero_one j (by linarith only [hx.1,hz.1,yr,hLU,ha])
      (by linarith only [hx.2,hz.2,yl,hWM,ha])

/-- The four LH inequalities, together with the width bounds, exclude every
integer horizontal wrap for one lower and one upper endpoint. -/
theorem lower_upper_no_up {L W Pz Uz Vz Mz P U V M ax ay az : ℝ} {j : ℤ}
    (hPz : 0 ≤ Pz) (hMz : 0 ≤ Mz) (hUz : Uz ≤ 1) (hVz : Vz ≤ 1)
    (hPV : Pz+2*W+2*V ≤ 1) (hPM : Pz+2*W+2*M ≤ 1)
    (hMU : Mz+2*L+2*U ≤ 1) (hMP : Mz+2*L+2*P ≤ 1)
    (hx : LowerArc L W ax) (hy : UpperArc P U V M ay)
    (hz : UpperArc Pz Uz Vz Mz az) (ha : ax+az-2*ay=(j:ℝ)) : False := by
  rcases hz with ⟨zl,zr⟩ | ⟨zl,zr⟩ <;> rcases hy with ⟨yl,yr⟩ | ⟨yl,yr⟩
  · exact no_int_neg_one_zero j (by linarith only [hx.1,zl,yr,hMP,hMz,hVz,ha])
      (by linarith only [hx.2,zr,yl,hPV,ha])
  · exact no_int_zero_one j (by linarith only [hx.1,zl,yr,hMU,hMz,hVz,ha])
      (by linarith only [hx.2,zr,yl,hPM,ha])
  · exact no_int_neg_one_zero j (by linarith only [hx.1,zl,yr,hMP,ha])
      (by linarith only [hx.2,zr,yl,hPV,hPz,hUz,ha])
  · exact no_int_zero_one j (by linarith only [hx.1,zl,yr,hMU,ha])
      (by linarith only [hx.2,zr,yl,hPM,hPz,hUz,ha])

#print axioms lower_lower_no_up
#print axioms lower_upper_no_up

end Erdos142BlockCertificate
