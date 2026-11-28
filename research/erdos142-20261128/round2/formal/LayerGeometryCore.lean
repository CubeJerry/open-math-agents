import StepCells

namespace Erdos142BlockCertificate

noncomputable section

structure Geometry where
  mem : ℝ → ℝ → ℝ → Prop
  separation : ℝ
  separation_pos : 0 < separation
  separation_le_one : separation ≤ 1
  bounds : ∀ {s a u : ℝ}, mem s a u →
    0 < s ∧ s < 1 ∧ |a| < 1/2 ∧ |u| < 1/2
  no_upward : ∀ {sx sy sz ax ay az ux uy uz : ℝ} {j : ℤ},
    mem sx ax ux → mem sy ay uy → mem sz az uz →
    2*sy=sx+sz+1 → ax+az-2*ay=(j:ℝ) → False
  angular_or_separated : ∀ {sx sy sz ax ay az ux uy uz : ℝ} {j : ℤ},
    mem sx ax ux → mem sy ay uy → mem sz az uz →
    2*sy=sx+sz → ax+az-2*ay=(j:ℝ) →
    (ax-az)^2 ≤ 4*(ux^2+uz^2-2*uy^2) ∨ separation ≤ |sx-sz|

def layerPotential (M s u : ℝ) : ℝ := M*s^2+4*u^2

theorem layerPotential_bounds (G : Geometry) {M s a u : ℝ}
    (hM : 2 ≤ M) (h : G.mem s a u) :
    0 ≤ layerPotential M s u ∧ layerPotential M s u ≤ M+1 := by
  obtain ⟨hs0,hs1,_,hu⟩ := G.bounds h
  have su : s^2 ≤ 1 := by nlinarith only [hs0,hs1]
  have uu : u^2 ≤ 1/4 := by
    obtain ⟨ul,ur⟩ := abs_lt.mp hu
    nlinarith [mul_nonneg (show 0 ≤ 1/2-u by linarith) (show 0 ≤ 1/2+u by linarith)]
  have ms : M*s^2 ≤ M := by
    simpa using mul_le_mul_of_nonneg_left su (by linarith only [hM] : 0≤M)
  unfold layerPotential
  constructor
  · positivity
  · linarith

theorem geometry_potential_gap (G : Geometry) {M : ℝ}
    (hM : 2 ≤ M) (hpay : 6 ≤ (M-2)*G.separation^2)
    {sx sy sz ax ay az ux uy uz : ℝ} {j k : ℤ}
    (hx : G.mem sx ax ux) (hy : G.mem sy ay uy) (hz : G.mem sz az uz)
    (hs : 2*sy=sx+sz+(k:ℝ)) (ha : ax+az-2*ay=(j:ℝ)) :
    (sx-sz)^2+(ax-az)^2 ≤
      layerPotential M sx ux+layerPotential M sz uz-2*layerPotential M sy uy := by
  obtain ⟨sx0,sx1,ax1,ux1⟩ := G.bounds hx
  obtain ⟨sy0,sy1,ay1,uy1⟩ := G.bounds hy
  obtain ⟨sz0,sz1,az1,uz1⟩ := G.bounds hz
  have kle : k ≤ 0 := by
    have klt : k < 2 := by exact_mod_cast (show (k:ℝ)<2 by linarith only [hs,sy1,sx0,sz0])
    by_contra hn
    have keq : k=1 := by omega
    subst k
    exact G.no_upward hx hy hz (by simpa using hs) ha
  have kleR : (k:ℝ) ≤ 0 := by exact_mod_cast kle
  have hcurv : (sx-sz)^2/2 ≤ sx^2+sz^2-2*sy^2 := by
    nlinarith only [mul_nonneg (show 0 ≤ (sx+sz)/2-sy by linarith only [hs,kleR])
      (show 0 ≤ (sx+sz)/2+sy by linarith only [sx0,sz0,sy0])]
  have pay_large (hlarge : G.separation^2/2 ≤ sx^2+sz^2-2*sy^2) :
      (sx-sz)^2+(ax-az)^2 ≤
        layerPotential M sx ux+layerPotential M sz uz-2*layerPotential M sy uy := by
    have paid : 3 ≤ (M-2)*(sx^2+sz^2-2*sy^2) := by
      have mul := mul_le_mul_of_nonneg_left hlarge (by linarith : 0 ≤ M-2)
      nlinarith only [mul,hpay]
    have aa : (ax-az)^2 ≤ 1 := by
      obtain ⟨xl,xr⟩ := abs_lt.mp ax1
      obtain ⟨zl,zr⟩ := abs_lt.mp az1
      nlinarith [mul_nonneg (show 0 ≤ 1-(ax-az) by linarith)
        (show 0 ≤ 1+(ax-az) by linarith)]
    have uu : uy^2 ≤ 1/4 := by
      obtain ⟨yl,yr⟩ := abs_lt.mp uy1
      nlinarith [mul_nonneg (show 0 ≤ 1/2-uy by linarith)
        (show 0 ≤ 1/2+uy by linarith)]
    unfold layerPotential
    nlinarith only [paid,hcurv,aa,uu,sq_nonneg ux,sq_nonneg uz]
  by_cases zero : k=0
  · subst k
    norm_num at hs
    rcases G.angular_or_separated hx hy hz hs ha with angular | separated
    · have paid : 0 ≤ (M-2)*(sx^2+sz^2-2*sy^2) :=
        mul_nonneg (by linarith) (by nlinarith only [hcurv,sq_nonneg (sx-sz)])
      unfold layerPotential
      nlinarith only [paid,hcurv,angular]
    · apply pay_large
      have sqbound := mul_le_mul separated separated G.separation_pos.le (abs_nonneg (sx-sz))
      simp only [← pow_two, sq_abs] at sqbound
      nlinarith only [hcurv,sqbound]
  · have kn : k ≤ -1 := by omega
    have knR : (k:ℝ) ≤ -1 := by exact_mod_cast kn
    have strong : 1/2 ≤ sx^2+sz^2-2*sy^2 := by
      nlinarith only [mul_nonneg
        (show 0 ≤ (sx+sz)/2-sy-1/2 by linarith only [hs,knR])
        (show 0 ≤ (sx+sz)/2+sy+1/2 by linarith only [sx0,sz0,sy0]),
        sq_nonneg (sx-sz),sy0]
    have sg := G.separation_pos
    have sl := G.separation_le_one
    apply pay_large
    nlinarith only [strong,sg,sl]

#print axioms geometry_potential_gap

end
end Erdos142BlockCertificate
