import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/- Source component: CoverCoordinateDerivatives -/
section
/-!
Differential identities for the sixth-root Fermat cover used by holdout.
The identities are proved for an arbitrary derivation of a characteristic
zero field. They therefore apply to the actual finite extensions of the
physical residue derivations, once the coordinate identities are supplied.
-/

noncomputable section

namespace HoldoutConstruction

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private theorem derivation_sixth_power (D : Derivation ℤ K K) (a : K) :
    D (a^6) = 6*a^5*D a := by
  simp only [Derivation.leibniz_pow, Nat.reduceSub, nsmul_eq_mul, smul_eq_mul]
  ring

/-- The differentiated Fermat relation, after cancelling the nonzero 6. -/
theorem fermat_cover_tangent_relation (D : Derivation ℤ K K) (a b : K)
    (hbase : a^6+b^6=1) : a^5*D a+b^5*D b=0 := by
  have h : D (a^6+b^6) = 0 := by
    rw [hbase, Derivation.map_one_eq_zero]
  rw [map_add, derivation_sixth_power, derivation_sixth_power] at h
  have hsix : (6 : K)*(a^5*D a+b^5*D b)=0 := by
    linear_combination h
  exact (mul_eq_zero.mp hsix).resolve_left (by norm_num)

/-- Differentiate t^6=Y0^6+Y2^6 in normalized coordinates
Y0=a*t, Y2=b*t. No division by t or a is needed for this identity. -/
theorem fermat_cover_time_derivative (D : Derivation ℤ K K)
    (a b t e0 e2 : K) (hbase : a^6+b^6=1)
    (h0 : D (a*t)=e0) (h2 : D (b*t)=e2) :
    D t = a^5*e0+b^5*e2 := by
  have hc := fermat_cover_tangent_relation D a b hbase
  have ha : a*D t+t*D a=e0 := by
    simpa only [Derivation.leibniz, smul_eq_mul] using h0
  have hb : b*D t+t*D b=e2 := by
    simpa only [Derivation.leibniz, smul_eq_mul] using h2
  linear_combination a^5*ha+b^5*hb-(D t)*hbase-t*hc

/-- The beta derivative in physical coordinate directions. -/
theorem fermat_cover_beta_derivative (D : Derivation ℤ K K)
    (a b t e0 e2 : K) (hbase : a^6+b^6=1) (ht : t≠0)
    (h0 : D (a*t)=e0) (h2 : D (b*t)=e2) :
    D b = (-b*a^5*e0+a^6*e2)/t := by
  apply (eq_div_iff ht).mpr
  have hb : b*D t+t*D b=e2 := by
    simpa only [Derivation.leibniz, smul_eq_mul] using h2
  rw [fermat_cover_time_derivative D a b t e0 e2 hbase h0 h2] at hb
  linear_combination hb-e2*hbase

/-- The symmetric alpha derivative, useful when checking that quotient
fiber derivatives fix the entire Fermat coefficient field. -/
theorem fermat_cover_alpha_derivative (D : Derivation ℤ K K)
    (a b t e0 e2 : K) (hbase : a^6+b^6=1) (ht : t≠0)
    (h0 : D (a*t)=e0) (h2 : D (b*t)=e2) :
    D a = (b^6*e0-a*b^5*e2)/t := by
  apply (eq_div_iff ht).mpr
  have ha : a*D t+t*D a=e0 := by
    simpa only [Derivation.leibniz, smul_eq_mul] using h0
  rw [fermat_cover_time_derivative D a b t e0 e2 hbase h0 h2] at ha
  linear_combination ha-e0*hbase

/-- In the beta chart, the alpha derivative is determined by the Fermat
relation. This statement uses only a≠0, without any assumption on t. -/
theorem fermat_cover_passive_derivative (D : Derivation ℤ K K)
    (a b : K) (hbase : a^6+b^6=1) (ha : a≠0) :
    D a = -(b^5*D b)/a^5 := by
  apply (eq_div_iff (pow_ne_zero 5 ha)).mpr
  linear_combination fermat_cover_tangent_relation D a b hbase

theorem fermat_cover_sum_derivative (D : Derivation ℤ K K)
    (a b t y e0 ey e2 : K) (hbase : a^6+b^6=1)
    (h0 : D (a*t)=e0) (hy : D y=ey) (h2 : D (b*t)=e2) :
    D (y^2+t^2) = 2*y*ey+2*t*(a^5*e0+b^5*e2) := by
  rw [map_add, Derivation.leibniz_pow, Derivation.leibniz_pow]
  simp only [Nat.reduceSub, pow_one, nsmul_eq_mul, smul_eq_mul, hy,
    fermat_cover_time_derivative D a b t e0 e2 hbase h0 h2]
  ring

theorem fermat_cover_product_derivative (D : Derivation ℤ K K)
    (a b t y e0 ey e2 : K) (hbase : a^6+b^6=1)
    (h0 : D (a*t)=e0) (hy : D y=ey) (h2 : D (b*t)=e2) :
    D (y*t) = t*ey+y*(a^5*e0+b^5*e2) := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul, hy,
    fermat_cover_time_derivative D a b t e0 e2 hbase h0 h2]
  ring

end HoldoutConstruction

#print axioms HoldoutConstruction.fermat_cover_time_derivative
#print axioms HoldoutConstruction.fermat_cover_beta_derivative
#print axioms HoldoutConstruction.fermat_cover_alpha_derivative
#print axioms HoldoutConstruction.fermat_cover_passive_derivative
#print axioms HoldoutConstruction.fermat_cover_sum_derivative
#print axioms HoldoutConstruction.fermat_cover_product_derivative
end
end
