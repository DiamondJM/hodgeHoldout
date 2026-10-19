import Proposal.EndpointFields
import Proposal.PolynomialCalculus
import Proposal.ResidueClearing
import Proposal.ResidueDerivatives

/- Source component: EndpointDerivations -/
section
/-!
Canonical commuting endpoint derivations on the conic coefficient field.
The three independent coordinates are X2, S and P; X0 is the simple root of
X0^6+X2^6+S^3-3*S*P^2. Every derivation is constructed through the actual
polynomial quotient and its fraction field.
-/

noncomputable section

namespace HoldoutConstruction

section Coordinates

variable {R : Type*} [CommRing R]

def endpointEquation : MvPolynomial (Fin 4) R :=
  MvPolynomial.X 0^6 + MvPolynomial.X 1^6 + MvPolynomial.X 2^3 -
    3*MvPolynomial.X 2*MvPolynomial.X 3^2

theorem endpointEquation_univariate :
    MvPolynomial.finSuccEquiv R 3 (endpointEquation (R := R)) =
      endpointPolynomial (R := R) := by
  have he : (Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 3) R))
      (fun j => Polynomial.C (MvPolynomial.X j))) =
      ![Polynomial.X, Polynomial.C (MvPolynomial.X 0),
        Polynomial.C (MvPolynomial.X 1), Polynomial.C (MvPolynomial.X 2)] := by
    funext i
    fin_cases i <;> rfl
  simp [endpointEquation, endpointPolynomial, MvPolynomial.finSuccEquiv_apply, he,
    Polynomial.C_ofNat]
  ring

def endpointQuotient : MvPolynomial (Fin 4) R →+* EndpointRing R :=
  (AdjoinRoot.mk (endpointPolynomial (R := R))).comp
    (MvPolynomial.finSuccEquiv R 3).toRingHom

theorem endpointQuotient_surjective : Function.Surjective (endpointQuotient (R := R)) :=
  (AdjoinRoot.mk_surjective (g := endpointPolynomial (R := R))).comp
    (MvPolynomial.finSuccEquiv R 3).surjective

theorem endpointQuotient_kernel (p : MvPolynomial (Fin 4) R) :
    endpointQuotient p = 0 ↔ endpointEquation ∣ p := by
  change AdjoinRoot.mk (endpointPolynomial (R := R))
    (MvPolynomial.finSuccEquiv R 3 p) = 0 ↔ _
  rw [AdjoinRoot.mk_eq_zero, ← endpointEquation_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv R 3)

@[simp] theorem endpointQuotient_X_zero :
    endpointQuotient (MvPolynomial.X (R := R) (0 : Fin 4)) = endpointRoot := by
  simp [endpointQuotient, endpointRoot, MvPolynomial.finSuccEquiv_apply]

@[simp] theorem endpointQuotient_X_succ (i : Fin 3) :
    endpointQuotient (MvPolynomial.X (R := R) i.succ) = endpointParameter i := by
  change AdjoinRoot.mk (endpointPolynomial (R := R))
    (MvPolynomial.finSuccEquiv R 3 (MvPolynomial.X i.succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  rfl

theorem endpointEquation_partial_zero :
    integerPartial (R := R) 0 endpointEquation = 6*MvPolynomial.X 0^5 := by
  norm_num [integerPartial, endpointEquation, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul, Pi.single_apply,
    show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 0 by decide]
  exact Derivation.map_natCast _ _

end Coordinates

abbrev EndpointField (R : Type*) [CommRing R] := FractionRing (EndpointRing R)

section Field

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

attribute [local instance] endpoint_adjoinRoot_isDomain endpoint_charZero

local instance : Algebra ℤ (EndpointField R) := Ring.toIntAlgebra _

def endpointResidueMap : MvPolynomial (Fin 4) R →+* EndpointField R :=
  (algebraMap (EndpointRing R) (EndpointField R)).comp endpointQuotient

omit [IsDomain R] [CharZero R] in
@[simp] theorem endpointResidueMap_C (r : R) :
    endpointResidueMap (MvPolynomial.C r) = algebraMap R (EndpointField R) r := by
  change algebraMap (EndpointRing R) (EndpointField R)
    (AdjoinRoot.mk (endpointPolynomial (R := R))
      (MvPolynomial.finSuccEquiv R 3 (MvPolynomial.C r))) = _
  rw [show MvPolynomial.finSuccEquiv R 3 (MvPolynomial.C r) =
    Polynomial.C (MvPolynomial.C r) from (MvPolynomial.finSuccEquiv R 3).commutes r]
  rfl

theorem endpointResidueMap_kernel (p : MvPolynomial (Fin 4) R) :
    endpointResidueMap p = 0 ↔ endpointEquation ∣ p :=
  residue_fractionMap_kernel endpointQuotient endpointEquation endpointQuotient_kernel p

omit [IsDomain R] [CharZero R] in
@[simp] theorem endpointResidueMap_X_zero :
    endpointResidueMap (MvPolynomial.X (R := R) (0 : Fin 4)) =
      algebraMap (EndpointRing R) (EndpointField R) endpointRoot := by
  simp [endpointResidueMap]

omit [IsDomain R] [CharZero R] in
@[simp] theorem endpointResidueMap_X_succ (i : Fin 3) :
    endpointResidueMap (MvPolynomial.X (R := R) i.succ) =
      algebraMap (EndpointRing R) (EndpointField R) (endpointParameter i) := by
  simp [endpointResidueMap]

omit [IsDomain R] in
theorem endpointResidue_root_ne_zero :
    algebraMap (EndpointRing R) (EndpointField R) (endpointRoot (R := R)) ≠ 0 := by
  simpa only [map_zero] using
    (IsFractionRing.injective (EndpointRing R) (EndpointField R)).ne
      (endpointRoot_ne_zero (R := R))

theorem endpoint_normal_ne_zero :
    endpointResidueMap (integerPartial (R := R) 0 endpointEquation) ≠ 0 := by
  rw [endpointEquation_partial_zero, map_mul, map_ofNat, map_pow, endpointResidueMap_X_zero]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 5 endpointResidue_root_ne_zero)

/-- Actual residue derivations with respect to the three independent
endpoint parameters. -/
def endpointTangent (i : Fin 3) : Derivation ℤ (EndpointField R) (EndpointField R) :=
  residueTangent (K := EndpointField R) (endpointQuotient (R := R)) endpointQuotient_surjective
    (integerPartial 0) (integerPartial i.succ) endpointEquation
    endpointQuotient_kernel endpoint_normal_ne_zero

theorem endpointTangent_apply (i : Fin 3) (p : MvPolynomial (Fin 4) R) :
    endpointTangent i (endpointResidueMap p) =
      endpointResidueMap (integerPartial i.succ p) -
        endpointResidueMap (integerPartial i.succ endpointEquation) /
          endpointResidueMap (integerPartial 0 endpointEquation) *
            endpointResidueMap (integerPartial 0 p) :=
  residueTangent_apply (K := EndpointField R) (endpointQuotient (R := R)) endpointQuotient_surjective
    (integerPartial 0) (integerPartial i.succ) endpointEquation
    endpointQuotient_kernel endpoint_normal_ne_zero p

theorem endpointTangents_commute (i j : Fin 3) :
    Function.Commute (endpointTangent (R := R) i) (endpointTangent j) :=
  residueTangent_commute (K := EndpointField R) (endpointQuotient (R := R)) endpointQuotient_surjective
    (integerPartial 0) (integerPartial i.succ) (integerPartial j.succ) endpointEquation
    endpointQuotient_kernel endpoint_normal_ne_zero
    (integerPartial_commute i.succ 0) (integerPartial_commute j.succ 0)
    (integerPartial_commute i.succ j.succ)

@[simp] theorem endpointTangent_constant (i : Fin 3) (r : R) :
    endpointTangent i (endpointResidueMap (MvPolynomial.C r)) = 0 := by
  rw [endpointTangent_apply]
  simp

@[simp] theorem endpointTangent_algebraMap (i : Fin 3) (r : R) :
    endpointTangent i (algebraMap R (EndpointField R) r) = 0 := by
  rw [← endpointResidueMap_C, endpointTangent_constant]

theorem endpointTangent_parameter (i j : Fin 3) :
    endpointTangent i
      (algebraMap (EndpointRing R) (EndpointField R) (endpointParameter j)) =
        if j = i then 1 else 0 := by
  rw [← endpointResidueMap_X_succ, endpointTangent_apply,
    integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j)]
  simp only [map_zero, mul_zero, sub_zero]
  by_cases hij : j = i
  · subst j
    simp
  · have hs : j.succ ≠ i.succ := fun h => hij (Fin.succ_injective _ h)
    simp [integerPartial_X_of_ne _ _ hs, hij]

theorem endpointTangent_root (i : Fin 3) :
    endpointTangent i
      (algebraMap (EndpointRing R) (EndpointField R) (endpointRoot (R := R))) =
        -endpointResidueMap (integerPartial i.succ endpointEquation) /
          endpointResidueMap (integerPartial 0 endpointEquation) := by
  rw [← endpointResidueMap_X_zero, endpointTangent_apply,
    integerPartial_X_of_ne i.succ 0 (Ne.symm (Fin.succ_ne_zero i)),
    integerPartial_X_self]
  simp only [map_zero, map_one, mul_one, zero_sub, neg_div]

end Field

end HoldoutConstruction

#print axioms HoldoutConstruction.endpoint_normal_ne_zero
#print axioms HoldoutConstruction.endpointTangents_commute
#print axioms HoldoutConstruction.endpointTangent_parameter
end
end
