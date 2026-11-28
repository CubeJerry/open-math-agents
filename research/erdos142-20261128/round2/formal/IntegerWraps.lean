import StepCells

namespace Erdos142BlockCertificate

lemma no_int_neg_one_zero (j : ℤ) (hl : (-1:ℝ)<(j:ℝ)) (hr : (j:ℝ)<0) : False := by
  have jl : -1<j := by exact_mod_cast hl
  have jr : j<0 := by exact_mod_cast hr
  omega

lemma no_int_zero_one (j : ℤ) (hl : (0:ℝ)<(j:ℝ)) (hr : (j:ℝ)<1) : False := by
  have jl : 0<j := by exact_mod_cast hl
  have jr : j<1 := by exact_mod_cast hr
  omega

lemma int_zero_of_unit_bounds (j : ℤ) (hl : (-1:ℝ)<(j:ℝ)) (hr : (j:ℝ)<1) : j=0 := by
  have jl : -1<j := by exact_mod_cast hl
  have jr : j<1 := by exact_mod_cast hr
  omega

end Erdos142BlockCertificate
