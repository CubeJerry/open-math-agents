import SixWidthsNoUp

/-!
Independent extension for upper arcs with signed parameters. This file does
not alter the checked D=192 construction. It isolates the positivity used by
the mixed lower/upper exclusion: nonnegative actual arc widths suffice.
-/

namespace Erdos142BlockCertificate

theorem lower_upper_no_up_signed {L W Pz Uz Vz Mz P U V M ax ay az : ℝ} {j : ℤ}
    (hPz : -1≤Pz) (hMz : -1≤Mz) (hUz : Uz≤1) (hVz : Vz≤1)
    (hPV : Pz+2*W+2*V≤1) (hPM : Pz+2*W+2*M≤1)
    (hMU : Mz+2*L+2*U≤1) (hMP : Mz+2*L+2*P≤1)
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

theorem lower_upper_no_up_of_arc_widths {L W Pz Uz Vz Mz P U V M ax ay az : ℝ}
    {j : ℤ} (hpositiveArc : 0≤Pz+Vz) (hnegativeArc : 0≤Mz+Uz)
    (hUz : Uz≤1) (hVz : Vz≤1)
    (hPV : Pz+2*W+2*V≤1) (hPM : Pz+2*W+2*M≤1)
    (hMU : Mz+2*L+2*U≤1) (hMP : Mz+2*L+2*P≤1)
    (hx : LowerArc L W ax) (hy : UpperArc P U V M ay)
    (hz : UpperArc Pz Uz Vz Mz az) (ha : ax+az-2*ay=(j:ℝ)) : False :=
  lower_upper_no_up_signed
    (by linarith only [hpositiveArc,hVz]) (by linarith only [hnegativeArc,hUz])
    hUz hVz hPV hPM hMU hMP hx hy hz ha

theorem lower_arc_bounds_signed {L W a : ℝ} (hL : L≤1) (hW : W≤1)
    (h : LowerArc L W a) : |a|<1/2 := by
  apply abs_lt.mpr
  constructor <;> linarith only [h.1,h.2,hL,hW]

#print axioms lower_upper_no_up_signed
#print axioms lower_upper_no_up_of_arc_widths
#print axioms lower_arc_bounds_signed

end Erdos142BlockCertificate
