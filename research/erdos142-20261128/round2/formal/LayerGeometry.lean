import BlockCertificate
import LayerGeometryCore

namespace Erdos142BlockCertificate

open QuandleResearch.Erdos142
noncomputable section

/-- Any finite discretization lying in a verified geometry inherits the
certificate consumed by the generic asymptotic theorem. -/
def certificateOfGeometry (p : ℕ) (hp : 0 < p) (G : Geometry) (M : ℝ)
    (hM : 2 ≤ M) (hpay : 6 ≤ (M-2)*G.separation^2)
    (B : Finset (ZMod p × ZMod p))
    (X Y : ZMod p × ZMod p → ℤ) (U : ZMod p × ZMod p → ℝ)
    (hlift : ∀ v ∈ B, (X v:ZMod p)=v.1 ∧ (Y v:ZMod p)=v.2)
    (hmem : ∀ v ∈ B, G.mem ((X v:ℝ)/(p:ℝ)) ((Y v:ℝ)/(p:ℝ)) (U v)) :
    Certificate p where
  block := B
  X := X
  Y := Y
  F := fun v => layerPotential M ((X v:ℝ)/(p:ℝ)) (U v)
  height := M+1
  lift := hlift
  bounds := fun v hv => layerPotential_bounds G hM (hmem v hv)
  gap := by
    intro x hx y hy z hz hAP
    have hsmod : (X x:ZMod p)+(X z:ZMod p)=2*(X y:ZMod p) := by
      rw [(hlift x hx).1,(hlift z hz).1,(hlift y hy).1,two_mul]
      exact congrArg Prod.fst hAP
    have hamod : (Y x:ZMod p)+(Y z:ZMod p)=2*(Y y:ZMod p) := by
      rw [(hlift x hx).2,(hlift z hz).2,(hlift y hy).2,two_mul]
      exact congrArg Prod.snd hAP
    obtain ⟨k,hk⟩ := normalized_modular_AP hp hsmod
    obtain ⟨j,hj⟩ := normalized_modular_AP hp hamod
    have hs : 2*((X y:ℝ)/(p:ℝ))=(X x:ℝ)/(p:ℝ)+(X z:ℝ)/(p:ℝ)+((-k:ℤ):ℝ) := by
      push_cast
      linarith
    have h := geometry_potential_gap G hM hpay (hmem x hx) (hmem y hy) (hmem z hz) hs hj
    push_cast
    simp only [sub_div]
    nlinarith only [h]

#print axioms geometry_potential_gap
#print axioms certificateOfGeometry

end
end Erdos142BlockCertificate
