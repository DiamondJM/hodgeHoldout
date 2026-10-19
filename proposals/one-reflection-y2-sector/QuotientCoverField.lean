import Proposal.CoverFields

/- Source component: QuotientCoverField -/
section
/-!
The weighted quotient function field over the generic Fermat coefficient
field embeds in the same common residue field as the physical hypersurface.
No finiteness assertion is needed for this direction of differential
transport. Prepared with OpenAI ChatGPT assistance for a contribution
through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] genericCommonCoverRing_isDomain
attribute [local instance] quotient_adjoinRoot_isDomain

abbrev GenericQuotientRing :=
  AdjoinRoot (quotientPolynomial (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))

abbrev GenericQuotientField := FractionRing GenericQuotientRing

def quotientCoordinateFieldMap : GenericQuotientRing →+* CommonCoverFunctionField :=
  (algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField).comp
    (quotientCommonCoverMap (genericBaseAlpha ℂ) (genericBaseAlpha ℂ))

theorem quotientCoordinateFieldMap_injective :
    Function.Injective quotientCoordinateFieldMap := by
  intro a b h
  apply quotientCommonCoverMap_injective (genericBaseAlpha ℂ) (genericBaseAlpha ℂ)
  exact IsFractionRing.injective (GenericCommonCoverRing ℂ) CommonCoverFunctionField h

/-- The exact quotient residue-field embedding. -/
def quotientCoverFieldMap : GenericQuotientField →+* CommonCoverFunctionField :=
  IsFractionRing.lift (K := GenericQuotientField) (g := quotientCoordinateFieldMap)
    quotientCoordinateFieldMap_injective

@[simp] theorem quotientCoverFieldMap_coordinateRing (r : GenericQuotientRing) :
    quotientCoverFieldMap (algebraMap GenericQuotientRing GenericQuotientField r) =
      algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
        (quotientCommonCoverMap (genericBaseAlpha ℂ) (genericBaseAlpha ℂ) r) := by
  simp [quotientCoverFieldMap, quotientCoordinateFieldMap, RingHom.comp_apply]

@[simp] theorem quotientCoverFieldMap_coefficient (c : FermatCoefficientField ℂ) :
    quotientCoverFieldMap (algebraMap (FermatCoefficientField ℂ) GenericQuotientField c) =
      algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField c := by
  rw [IsScalarTower.algebraMap_apply (FermatCoefficientField ℂ)
    GenericQuotientRing GenericQuotientField, quotientCoverFieldMap_coordinateRing]
  change algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
    (quotientCommonCoverMap _ _ (AdjoinRoot.of _ (MvPolynomial.C c))) = _
  simp only [quotientCommonCoverMap, AdjoinRoot.map_of,
    quotientCoverCoefficientMap, MvPolynomial.eval₂Hom_C]
  change algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
    (algebraMap (FermatCoefficientField ℂ) (GenericCommonCoverRing ℂ) c) = _
  exact (IsScalarTower.algebraMap_apply (FermatCoefficientField ℂ)
    (GenericCommonCoverRing ℂ) CommonCoverFunctionField c).symm

/-- The displayed common-cover coordinates. The polynomial coordinates
have order X1,X2,y,T; X0 is the separately adjoined monic root. -/
def coverCoefficient (i : Fin 4) : CommonCoverFunctionField :=
  algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
    (AdjoinRoot.of _ (MvPolynomial.X i))

def coverX0 : CommonCoverFunctionField :=
  algebraMap (GenericCommonCoverRing ℂ) CommonCoverFunctionField
    (AdjoinRoot.root (commonCoverPolynomial (genericBaseAlpha ℂ) (genericBaseAlpha ℂ)))

abbrev coverX1 := coverCoefficient 0
abbrev coverX2 := coverCoefficient 1
abbrev coverY := coverCoefficient 2
abbrev coverT := coverCoefficient 3

def coverAlpha : CommonCoverFunctionField :=
  algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField (genericBaseAlpha ℂ)

def coverBeta : CommonCoverFunctionField :=
  algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField (genericBaseBeta ℂ)

theorem cover_fermat_relation : coverAlpha^6 + coverBeta^6 = 1 := by
  have hb : (genericBaseAlpha ℂ)^6 + (genericBaseBeta ℂ)^6 = 1 := by
    have h := congrArg (algebraMap (FermatBaseRing ℂ) (FermatCoefficientField ℂ))
      (fermat_base_relation (R := ℂ))
    simpa only [map_add, map_pow, map_one, genericBaseAlpha, genericBaseBeta] using h
  have h := congrArg (algebraMap (FermatCoefficientField ℂ) CommonCoverFunctionField) hb
  simpa only [map_add, map_pow, map_one, coverAlpha, coverBeta] using h

end HoldoutConstruction

#print axioms HoldoutConstruction.quotientCoverFieldMap
#print axioms HoldoutConstruction.quotientCoverFieldMap_coefficient
#print axioms HoldoutConstruction.cover_fermat_relation
end
end
