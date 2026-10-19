import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Proposal.CommonCoverDomain
import Proposal.FermatFields

/- Source component: QuotientCoverEmbedding -/
section
/-!
The weighted quotient embeds into the common cover. Injectivity is proved
by an explicit square-root lift over an algebraically closed field, then
descended along an injective coefficient map. This is an algebraic
construction lemma, not a certificate. Prepared with OpenAI ChatGPT
assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

section CoefficientMap

variable {R : Type*} [CommRing R]

/-- The source coefficient order is X1,X2,S,P; the target coefficient
order is X1,X2,y,T. -/
def quotientCoverCoefficientMap :
    MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![MvPolynomial.X 0, MvPolynomial.X 1,
      MvPolynomial.X 2^2 + MvPolynomial.X 3^2,
      MvPolynomial.X 2 * MvPolynomial.X 3]

theorem quotientCoverCoefficientMap_map {K : Type*} [CommRing K]
    (φ : R →+* K) :
    (MvPolynomial.map φ).comp (quotientCoverCoefficientMap (R := R)) =
      (quotientCoverCoefficientMap (R := K)).comp (MvPolynomial.map φ) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [quotientCoverCoefficientMap]
  · intro i
    fin_cases i <;> simp [quotientCoverCoefficientMap]

end CoefficientMap

section AlgebraicallyClosed

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- Square roots of S+2P and S-2P give an explicit lift of every pair of
quadratic invariants. -/
theorem quadratic_cover_surjective (S P : K) :
    ∃ y T : K, y^2 + T^2 = S ∧ y * T = P := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (S + 2*P) (show 0 < 2 by decide)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (S - 2*P) (show 0 < 2 by decide)
  refine ⟨(a+b)/2, (a-b)/2, ?_, ?_⟩
  · field_simp
    linear_combination 2*ha + 2*hb
  · field_simp
    linear_combination ha - hb

theorem quotientCoverCoefficientMap_injective_algClosed :
    Function.Injective (quotientCoverCoefficientMap (R := K)) := by
  apply polynomialMap_injective_of_dense_evaluations
    (quotientCoverCoefficientMap (R := K)) 1 one_ne_zero
  intro x _
  obtain ⟨y, t, hS, hP⟩ := quadratic_cover_surjective (x 2) (x 3)
  let e : MvPolynomial (Fin 4) K →+* K := MvPolynomial.eval ![x 0, x 1, y, t]
  have he : e.comp (quotientCoverCoefficientMap (R := K)) = MvPolynomial.eval x := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e, quotientCoverCoefficientMap]
    · intro i
      fin_cases i <;> simp [e, quotientCoverCoefficientMap, hS, hP]
  exact ⟨e, fun p => RingHom.congr_fun he p⟩

end AlgebraicallyClosed

section Injectivity

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- Coefficient-map injectivity holds over an arbitrary characteristic-zero
domain, including the Fermat-curve coordinate domain. -/
theorem quotientCoverCoefficientMap_injective :
    Function.Injective (quotientCoverCoefficientMap (R := R)) := by
  let K := AlgebraicClosure (FractionRing R)
  let φ : R →+* K :=
    (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hφ : Function.Injective φ :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R _)
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hzero : quotientCoverCoefficientMap (MvPolynomial.map φ p) = 0 := by
    have hcomm := RingHom.congr_fun (quotientCoverCoefficientMap_map φ) p
    simp only [RingHom.comp_apply] at hcomm
    rw [← hcomm, hp, map_zero]
  apply MvPolynomial.map_injective φ hφ
  apply quotientCoverCoefficientMap_injective_algClosed (K := K)
  simpa only [map_zero] using hzero

end Injectivity

section Hypersurface

variable {R : Type*} [CommRing R]

/-- Exact equation compatibility with the fixed S,P ordering. -/
theorem quotientPolynomial_commonCover (alpha beta : R) :
    (quotientPolynomial alpha beta).map quotientCoverCoefficientMap =
      commonCoverPolynomial alpha beta := by
  simp [quotientPolynomial, commonCoverPolynomial, quotientCoverCoefficientMap,
    -MvPolynomial.eval₂Hom_C_eq_bind₁, map_ofNat]
  ring

private theorem adjoinRoot_map_injective_of_eq
    {C D : Type*} [CommRing C] [CommRing D]
    (φ : C →+* D) (hφ : Function.Injective φ)
    (f : Polynomial C) (hf : f.Monic) (g : Polynomial D)
    (hfg : f.map φ = g) (hdiv : g ∣ f.map φ) :
    Function.Injective (AdjoinRoot.map φ f g hdiv) := by
  subst g
  exact adjoinRoot_map_injective φ hφ f hf

/-- The exact quotient coordinate ring maps into the common cover. -/
def quotientCommonCoverMap (alpha beta : R) :
    AdjoinRoot (quotientPolynomial alpha beta) →+*
      AdjoinRoot (commonCoverPolynomial alpha beta) :=
  AdjoinRoot.map quotientCoverCoefficientMap
    (quotientPolynomial alpha beta) (commonCoverPolynomial alpha beta)
    (by rw [quotientPolynomial_commonCover])

theorem quotientCommonCoverMap_injective [IsDomain R] [CharZero R]
    (alpha beta : R) : Function.Injective (quotientCommonCoverMap alpha beta) := by
  exact adjoinRoot_map_injective_of_eq quotientCoverCoefficientMap
    quotientCoverCoefficientMap_injective _ (quotientPolynomial_monic alpha beta)
    _ (quotientPolynomial_commonCover alpha beta) _

end Hypersurface

end HoldoutConstruction

#print axioms HoldoutConstruction.quadratic_cover_surjective
#print axioms HoldoutConstruction.quotientCoverCoefficientMap_injective
#print axioms HoldoutConstruction.quotientCommonCoverMap_injective
end
end
