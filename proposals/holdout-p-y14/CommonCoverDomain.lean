import Proposal.HypersurfaceDomain

/- Source component: CommonCoverDomain -/
section
/-!
An integral common cover for the weighted quotient and the exact holdout
hypersurface. This is a generic domain lemma, not a certificate.

The proof follows the monic-specialization and Eisenstein pattern proved
in HypersurfaceDomain during this collaboration, using the credited
Lean/mathlib polynomial infrastructure. Prepared with OpenAI ChatGPT
assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

section CommonCover

variable {R : Type*} [CommRing R]

/-- The common cover as a monic polynomial in X0. Its four coefficient
variables are X1, X2, y, and T, in that order. -/
def commonCoverPolynomial (alpha beta : R) : (MvPolynomial (Fin 4) R)[X] :=
  X^6 +
    (C (MvPolynomial.C alpha * MvPolynomial.X 0 *
        MvPolynomial.X 2 * MvPolynomial.X 3) * X^3 +
      C (MvPolynomial.X 0^6 + MvPolynomial.X 1^6 +
        MvPolynomial.X 2^6 + MvPolynomial.X 3^6 +
        MvPolynomial.C beta * MvPolynomial.X 0^3 * MvPolynomial.X 1 *
          MvPolynomial.X 2 * MvPolynomial.X 3))

theorem commonCoverPolynomial_monic (alpha beta : R) :
    (commonCoverPolynomial alpha beta).Monic := by
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 3 _) (by decide)
  · exact lt_of_le_of_lt degree_C_le (by decide)

/-- Set X1=X2=0, T=1, and translate y by a sixth root of -1. -/
def commonCoverSpecialization (eta : R) : MvPolynomial (Fin 4) R →+* R[X] :=
  MvPolynomial.eval₂Hom C ![0, 0, X + C eta, 1]

theorem commonCoverPolynomial_specialization (alpha beta eta : R) :
    (commonCoverPolynomial alpha beta).map (commonCoverSpecialization eta) =
      (X : (R[X])[X])^6 + C ((X + C eta)^6 + 1) := by
  simp [commonCoverPolynomial, commonCoverSpecialization]

/-- The common-cover equation is irreducible without any further
restriction on alpha and beta. In particular it is irreducible over the
entire Fermat-curve coefficient domain. -/
theorem commonCoverPolynomial_irreducible [IsDomain R] [CharZero R]
    (alpha beta eta : R) (heta : eta^6 = -1) :
    Irreducible (commonCoverPolynomial alpha beta) := by
  have heta0 : eta ≠ 0 := by
    rintro rfl
    norm_num at heta
  apply (commonCoverPolynomial_monic alpha beta).irreducible_of_irreducible_map
    (commonCoverSpecialization eta)
  rw [commonCoverPolynomial_specialization]
  apply irreducible_power_add_constant ((X + C eta)^6 + 1 : R[X])
  · simp [coeff_X_add_C_pow, heta]
  · have hc : (((X + C eta)^6 + 1 : R[X]).coeff 1) = 6 * eta^5 := by
      simp [coeff_X_add_C_pow, coeff_one, mul_comm]
    rw [hc]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ heta0)
  · decide

theorem commonCoverPolynomial_map {T : Type*} [CommRing T]
    (φ : R →+* T) (alpha beta : R) :
    (commonCoverPolynomial alpha beta).map (MvPolynomial.map φ) =
      commonCoverPolynomial (φ alpha) (φ beta) := by
  simp [commonCoverPolynomial]

/-- Monicity descends common-cover domainhood from the coefficient fraction
field. No rational coefficient is evaluated at a chosen seed point. -/
theorem commonCover_adjoinRoot_isDomain [IsDomain R] [CharZero R]
    (alpha beta eta : R) (heta : eta^6 = -1) :
    IsDomain (AdjoinRoot (commonCoverPolynomial alpha beta)) := by
  let φ : R →+* FractionRing R := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have heta' : (φ eta)^6 = -1 := by
    rw [← map_pow, heta, map_neg, map_one]
  have hmap : IsDomain (AdjoinRoot
      ((commonCoverPolynomial alpha beta).map (MvPolynomial.map φ))) := by
    rw [commonCoverPolynomial_map]
    exact AdjoinRoot.isDomain_of_prime
      (commonCoverPolynomial_irreducible (φ alpha) (φ beta) (φ eta) heta').prime
  let := hmap
  exact adjoinRoot_isDomain_of_monic_map (MvPolynomial.map φ)
    (MvPolynomial.map_injective φ hφ) _ (commonCoverPolynomial_monic alpha beta)

end CommonCover

end HoldoutConstruction

#print axioms HoldoutConstruction.commonCoverPolynomial_irreducible
#print axioms HoldoutConstruction.commonCover_adjoinRoot_isDomain
end
end
