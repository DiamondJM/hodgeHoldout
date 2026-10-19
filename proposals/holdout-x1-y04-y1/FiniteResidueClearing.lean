import Proposal.FiniteDifferentials
import Proposal.FiniteTrace
import Proposal.ResidueClearing
import Proposal.ResidueDerivatives

/- Source component: FiniteResidueClearing -/
section
/-!
Finite-field residue descent followed by legal polynomial clearing.

This closes the algebraic portion of a construction once a weighted
divergence solution has been obtained on a finite extension of the residue
function field. Homogeneity is deliberately a separate conclusion to prove.
Prepared with OpenAI ChatGPT assistance for a contribution through GitHub
account fqlx. The trace and differential-field infrastructure is due to the
Lean/mathlib authors; the specific residue normalization is proved here.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

section TraceEquation

variable {K L ι : Type*} [Field K] [Field L] [CharZero K]
variable [Algebra K L] [FiniteDimensional K L] [Fintype ι]

/-- The extension source may itself vary over the cover; the descended
source is its normalized trace. -/
theorem finiteNormalizedTrace_residue_equation_value
    (E : ι → Derivation ℤ K K) (E' : ι → Derivation ℤ L L)
    (compatible : ∀ i x, E' i (algebraMap K L x) = algebraMap K L (E i x))
    (g : K) (r : L) (w : ι → L)
    (equation : r +
      ∑ i, (E' i (w i) - w i * E' i (algebraMap K L g) / algebraMap K L g) = 0) :
    Algebra.normalizedTrace K L r +
      ∑ i, (E i (Algebra.normalizedTrace K L (w i)) -
        Algebra.normalizedTrace K L (w i) * E i g / g) = 0 := by
  have hlocal (i : ι) :
      Algebra.normalizedTrace K L
        (E' i (w i) - w i * E' i (algebraMap K L g) / algebraMap K L g) =
      E i (Algebra.normalizedTrace K L (w i)) -
        Algebra.normalizedTrace K L (w i) * E i g / g := by
    rw [compatible i g, map_sub,
      finiteNormalizedTrace_derivation (E i) (E' i) (compatible i)]
    congr 1
    calc
      _ = Algebra.normalizedTrace K L ((E i g / g) • w i) := by
        congr 1
        simp only [Algebra.smul_def, map_div₀]
        ring
      _ = (E i g / g) • Algebra.normalizedTrace K L (w i) := map_smul _ _ _
      _ = Algebra.normalizedTrace K L (w i) * E i g / g := by
        change (E i g / g) * Algebra.normalizedTrace K L (w i) = _
        ring
  have ht := congrArg (Algebra.normalizedTrace K L) equation
  simpa only [map_add, map_sum, map_zero, hlocal] using ht

/-- Normalized trace preserves the residue divergence equation, including
its density correction. No Galois hypothesis is required. -/
theorem finiteNormalizedTrace_residue_equation
    (E : ι → Derivation ℤ K K) (E' : ι → Derivation ℤ L L)
    (compatible : ∀ i x, E' i (algebraMap K L x) = algebraMap K L (E i x))
    (g r : K) (w : ι → L)
    (equation : algebraMap K L r +
      ∑ i, (E' i (w i) - w i * E' i (algebraMap K L g) / algebraMap K L g) = 0) :
    r + ∑ i, (E i (Algebra.normalizedTrace K L (w i)) -
      Algebra.normalizedTrace K L (w i) * E i g / g) = 0 := by
  have ht := finiteNormalizedTrace_residue_equation_value E E' compatible
    g (algebraMap K L r) w equation
  simpa only [Algebra.normalizedTrace_algebraMap_apply_eq_self] using ht

end TraceEquation

section Clearing

variable {R B K L ι : Type*} [CommRing R] [CommRing B] [IsDomain B]
variable [Field K] [Algebra B K] [IsFractionRing B K] [CharZero K]
variable [Field L] [Algebra K L] [FiniteDimensional K L] [Fintype ι]

/-- A weighted tangent solution on any finite field extension of the residue
field supplies legal polynomial denominator and numerator data, with the
full pole-order-one defect. The quotient and every compatibility assumption
are explicit; no homogeneity or vanishing of the final defect is assumed. -/
theorem finite_residue_solution_clearing
    (π : R →+* B) (surjective : Function.Surjective π)
    (Δ₀ : Derivation ℤ R R) (Δ : ι → Derivation ℤ R R)
    (E : ι → Derivation ℤ K K) (E' : ι → Derivation ℤ L L)
    (f A : R) (w : ι → L)
    (irreducible : Irreducible f)
    (kernel : ∀ p, π p = 0 ↔ f ∣ p)
    (g₀_ne : algebraMap B K (π (Δ₀ f)) ≠ 0)
    (mixed : ∀ i, Δ i (Δ₀ f) = Δ₀ (Δ i f))
    (compatible : ∀ i p, E i (algebraMap B K (π p)) =
      algebraMap B K (π (Δ i p)) -
        algebraMap B K (π (Δ i f)) / algebraMap B K (π (Δ₀ f)) *
          algebraMap B K (π (Δ₀ p)))
    (compatible' : ∀ i x, E' i (algebraMap K L x) = algebraMap K L (E i x))
    (equation :
      algebraMap K L
        ((algebraMap B K (π (Δ₀ A)) * algebraMap B K (π (Δ₀ f)) -
          algebraMap B K (π A) * algebraMap B K (π (Δ₀ (Δ₀ f)))) /
          (algebraMap B K (π (Δ₀ f)))^2) +
        ∑ i, (E' i (w i) -
          w i * E' i (algebraMap K L (algebraMap B K (π (Δ₀ f)))) /
            algebraMap K L (algebraMap B K (π (Δ₀ f)))) = 0) :
    ∃ D N₀ : R, ∃ N : ι → R, ∃ Q : R,
      D ≠ 0 ∧ IsRelPrime f D ∧
      (N₀ * Δ₀ f + ∑ i, N i * Δ i f = A * D) ∧
      (residueDivNum Δ₀ Δ D N₀ N = f * Q) ∧
      A * D^2 - D * (N₀ * Δ₀ f + ∑ i, N i * Δ i f) +
        f * residueDivNum Δ₀ Δ D N₀ N = f^2 * Q := by
  let v : ι → K := fun i => Algebra.normalizedTrace K L (w i)
  have heq := finiteNormalizedTrace_residue_equation E E' compatible'
    (algebraMap B K (π (Δ₀ f)))
    ((algebraMap B K (π (Δ₀ A)) * algebraMap B K (π (Δ₀ f)) -
      algebraMap B K (π A) * algebraMap B K (π (Δ₀ (Δ₀ f)))) /
      (algebraMap B K (π (Δ₀ f)))^2) w equation
  exact residue_solution_clearing ((algebraMap B K).comp π)
    Δ₀ Δ E f A v irreducible
    (residue_fractionMap_kernel π f kernel) g₀_ne mixed compatible
    (residue_common_representatives π surjective v) heq

/-- The same descent theorem using the actual tangent derivations constructed
from the quotient and their unique finite-field extensions. -/
theorem finite_residue_solution_clearing_canonical
    (π : R →+* B) (surjective : Function.Surjective π)
    (Δ₀ : Derivation ℤ R R) (Δ : ι → Derivation ℤ R R)
    (f A : R) (w : ι → L)
    (irreducible : Irreducible f)
    (kernel : ∀ p, π p = 0 ↔ f ∣ p)
    (g₀_ne : algebraMap B K (π (Δ₀ f)) ≠ 0)
    (mixed : ∀ i, Δ i (Δ₀ f) = Δ₀ (Δ i f))
    (equation :
      let E := fun i => residueTangent π surjective Δ₀ (Δ i) f kernel g₀_ne
      let E' := fun i => extendFiniteDerivation (L := L) (E i)
      algebraMap K L
        ((algebraMap B K (π (Δ₀ A)) * algebraMap B K (π (Δ₀ f)) -
          algebraMap B K (π A) * algebraMap B K (π (Δ₀ (Δ₀ f)))) /
          (algebraMap B K (π (Δ₀ f)))^2) +
        ∑ i, (E' i (w i) -
          w i * E' i (algebraMap K L (algebraMap B K (π (Δ₀ f)))) /
            algebraMap K L (algebraMap B K (π (Δ₀ f)))) = 0) :
    ∃ D N₀ : R, ∃ N : ι → R, ∃ Q : R,
      D ≠ 0 ∧ IsRelPrime f D ∧
      (N₀ * Δ₀ f + ∑ i, N i * Δ i f = A * D) ∧
      (residueDivNum Δ₀ Δ D N₀ N = f * Q) ∧
      A * D^2 - D * (N₀ * Δ₀ f + ∑ i, N i * Δ i f) +
        f * residueDivNum Δ₀ Δ D N₀ N = f^2 * Q := by
  apply finite_residue_solution_clearing π surjective Δ₀ Δ
    (fun i => residueTangent π surjective Δ₀ (Δ i) f kernel g₀_ne)
    (fun i => extendFiniteDerivation (L := L)
      (residueTangent π surjective Δ₀ (Δ i) f kernel g₀_ne))
    f A w irreducible kernel g₀_ne mixed
  · intro i p
    exact residueTangent_apply π surjective Δ₀ (Δ i) f kernel g₀_ne p
  · intro i x
    exact extendFiniteDerivation_apply _ x
  · exact equation

/-- A finite-cover solution also clears legally when its source is not a
base-field element, provided the exact normalized source trace is proved.
This is the form used to remove nontrivial deck characters. -/
theorem finite_residue_solution_clearing_value
    (π : R →+* B) (surjective : Function.Surjective π)
    (Δ₀ : Derivation ℤ R R) (Δ : ι → Derivation ℤ R R)
    (E : ι → Derivation ℤ K K) (E' : ι → Derivation ℤ L L)
    (f A : R) (source : L) (w : ι → L)
    (irreducible : Irreducible f)
    (kernel : ∀ p, π p = 0 ↔ f ∣ p)
    (g₀_ne : algebraMap B K (π (Δ₀ f)) ≠ 0)
    (mixed : ∀ i, Δ i (Δ₀ f) = Δ₀ (Δ i f))
    (compatible : ∀ i p, E i (algebraMap B K (π p)) =
      algebraMap B K (π (Δ i p)) -
        algebraMap B K (π (Δ i f)) / algebraMap B K (π (Δ₀ f)) *
          algebraMap B K (π (Δ₀ p)))
    (compatible' : ∀ i x, E' i (algebraMap K L x) = algebraMap K L (E i x))
    (source_trace : Algebra.normalizedTrace K L source =
      (algebraMap B K (π (Δ₀ A)) * algebraMap B K (π (Δ₀ f)) -
        algebraMap B K (π A) * algebraMap B K (π (Δ₀ (Δ₀ f)))) /
        (algebraMap B K (π (Δ₀ f)))^2)
    (equation : source +
      ∑ i, (E' i (w i) -
        w i * E' i (algebraMap K L (algebraMap B K (π (Δ₀ f)))) /
          algebraMap K L (algebraMap B K (π (Δ₀ f)))) = 0) :
    ∃ D N₀ : R, ∃ N : ι → R, ∃ Q : R,
      D ≠ 0 ∧ IsRelPrime f D ∧
      (N₀ * Δ₀ f + ∑ i, N i * Δ i f = A * D) ∧
      (residueDivNum Δ₀ Δ D N₀ N = f * Q) ∧
      A * D^2 - D * (N₀ * Δ₀ f + ∑ i, N i * Δ i f) +
        f * residueDivNum Δ₀ Δ D N₀ N = f^2 * Q := by
  let v : ι → K := fun i => Algebra.normalizedTrace K L (w i)
  have heq := finiteNormalizedTrace_residue_equation_value E E' compatible'
    (algebraMap B K (π (Δ₀ f))) source w equation
  rw [source_trace] at heq
  exact residue_solution_clearing ((algebraMap B K).comp π)
    Δ₀ Δ E f A v irreducible
    (residue_fractionMap_kernel π f kernel) g₀_ne mixed compatible
    (residue_common_representatives π surjective v) heq

end Clearing

end HoldoutConstruction

#print axioms HoldoutConstruction.finiteNormalizedTrace_residue_equation
#print axioms HoldoutConstruction.finiteNormalizedTrace_residue_equation_value
#print axioms HoldoutConstruction.finite_residue_solution_clearing
#print axioms HoldoutConstruction.finite_residue_solution_clearing_canonical
#print axioms HoldoutConstruction.finite_residue_solution_clearing_value
end
end
