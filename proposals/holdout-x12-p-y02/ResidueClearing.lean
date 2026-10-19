import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic

/- Source component: ResidueClearing -/
section
/-!
Legal clearing of a rational tangent solution on a hypersurface.

All statements are algebraic and independent of homogeneity. In particular,
this file does not assert a `HasCertificate` statement. Prepared with OpenAI
ChatGPT assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

section Representatives

variable {R B K ι : Type*} [CommRing R] [CommRing B] [IsDomain B]
variable [Field K] [Algebra B K] [IsFractionRing B K] [Fintype ι]

omit [IsDomain B] in
/-- Passing from a domain to its fraction field preserves the kernel of a
polynomial quotient map. -/
theorem residue_fractionMap_kernel (π : R →+* B) (f : R)
    (kernel : ∀ p, π p = 0 ↔ f ∣ p) (p : R) :
    ((algebraMap B K).comp π) p = 0 ↔ f ∣ p := by
  change algebraMap B K (π p) = 0 ↔ f ∣ p
  rw [← map_zero (algebraMap B K), (IsFractionRing.injective B K).eq_iff, kernel]

/-- A finite family in the fraction field of a quotient has polynomial
representatives with one common denominator nonzero on that quotient. -/
theorem residue_common_representatives (π : R →+* B)
    (surjective : Function.Surjective π) (w : ι → K) :
    ∃ d : R, ∃ n : ι → R,
      algebraMap B K (π d) ≠ 0 ∧
      ∀ i, algebraMap B K (π (n i)) = algebraMap B K (π d) * w i := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors B) w
  choose a ha using hb
  obtain ⟨d, hd⟩ := surjective (b : B)
  choose n hn using fun i => surjective (a i)
  refine ⟨d, n, ?_, ?_⟩
  · rw [hd]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
  · intro i
    rw [hn i, hd]
    simpa only [Algebra.smul_def] using ha i

end Representatives

section Clearing

variable {R K ι : Type*} [CommRing R] [Field K] [Fintype ι]

/-- Clearing and enforcing the distinguished normal component gives an exact
normal source identity, independent of any residue equation. -/
theorem cleared_normal_source (A d g₀ : R) (g n : ι → R) :
    (A * d - ∑ i, g i * n i) * g₀ +
      ∑ i, (g₀ * n i) * g i = A * (g₀ * d) := by
  rw [sub_mul, Finset.sum_mul]
  simp_rw [show ∀ i, g i * n i * g₀ = g₀ * n i * g i by intro i; ring]
  ring

/-- Nonzero reduction of a denominator is the exact legality condition when
the hypersurface equation is irreducible. -/
theorem legal_of_residue_ne_zero (ρ : R →+* K) (f D : R)
    (irreducible : Irreducible f) (kernel : ∀ p, ρ p = 0 ↔ f ∣ p)
    (nonzero : ρ D ≠ 0) : D ≠ 0 ∧ IsRelPrime f D := by
  refine ⟨?_, irreducible.isRelPrime_iff_not_dvd.mpr ?_⟩
  · intro h
    exact nonzero (by rw [h, map_zero])
  · exact fun h => nonzero ((kernel D).mpr h)

/-- The usual numerator of the divergence of `(N₀,N)/D`. -/
def residueDivNum (Δ₀ : Derivation ℤ R R) (Δ : ι → Derivation ℤ R R)
    (D N₀ : R) (N : ι → R) : R :=
  D * (Δ₀ N₀ + ∑ i, Δ i (N i)) -
    (N₀ * Δ₀ D + ∑ i, N i * Δ i D)

/-- The weighted residue divergence agrees with the reduction of the ambient
divergence once the normal source identity holds exactly. Only mixed
derivatives of the equation itself need to commute. -/
theorem residue_divergence_identity
    (ρ : R →+* K) (Δ₀ : Derivation ℤ R R) (Δ : ι → Derivation ℤ R R)
    (E : ι → Derivation ℤ K K)
    (A D N₀ g₀ : R) (N g : ι → R) (w : ι → K)
    (g₀_ne : ρ g₀ ≠ 0)
    (mixed : ∀ i, Δ i g₀ = Δ₀ (g i))
    (compatible : ∀ i p, E i (ρ p) =
      ρ (Δ i p) - ρ (g i) / ρ g₀ * ρ (Δ₀ p))
    (representative : ∀ i, ρ (N i) = ρ D * w i)
    (normal : N₀ * g₀ + ∑ i, N i * g i = A * D) :
    ρ (residueDivNum Δ₀ Δ D N₀ N) = (ρ D)^2 *
      ((ρ (Δ₀ A) * ρ g₀ - ρ A * ρ (Δ₀ g₀)) / (ρ g₀)^2 +
        ∑ i, (E i (w i) - w i * E i (ρ g₀) / ρ g₀)) := by
  have hnormal := congrArg ρ normal
  simp only [map_add, map_sum, map_mul] at hnormal
  have hderivative := congrArg (fun p => ρ (Δ₀ p)) normal
  simp only [map_add, map_sum, Derivation.leibniz, smul_eq_mul, map_mul,
    Finset.sum_add_distrib] at hderivative
  have hlocal (i : ι) :
      (ρ g₀)^2 * (ρ D)^2 * (E i (w i) - w i * E i (ρ g₀) / ρ g₀) =
      (ρ g₀)^2 * (ρ D * ρ (Δ i (N i)) - ρ (N i) * ρ (Δ i D)) -
        (ρ g₀ * ρ D) * (ρ (g i) * ρ (Δ₀ (N i)) +
          ρ (N i) * ρ (Δ₀ (g i))) +
        (ρ g₀ * ρ (Δ₀ D) + ρ D * ρ (Δ₀ g₀)) * (ρ (N i) * ρ (g i)) := by
    have he := congrArg (E i) (representative i)
    simp only [compatible, Derivation.leibniz, smul_eq_mul] at he
    rw [compatible i g₀, mixed i, representative i]
    linear_combination (norm := skip) -(ρ g₀)^2 * ρ D * he
    field_simp [g₀_ne]
    ring
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => hlocal i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum] at hsum
  have hr : (ρ g₀)^2 * (ρ D)^2 *
      ((ρ (Δ₀ A) * ρ g₀ - ρ A * ρ (Δ₀ g₀)) / (ρ g₀)^2) =
      (ρ D)^2 * (ρ (Δ₀ A) * ρ g₀ - ρ A * ρ (Δ₀ g₀)) := by
    field_simp
  apply mul_left_cancel₀ (pow_ne_zero 2 g₀_ne)
  simp only [residueDivNum, map_sub, map_mul, map_add, map_sum]
  conv_rhs => rw [← mul_assoc, mul_add, hr, Finset.sum_sub_distrib, hsum]
  linear_combination ρ g₀ * ρ D * hderivative -
    (ρ g₀ * ρ (Δ₀ D) + ρ D * ρ (Δ₀ g₀)) * hnormal

/-- A rational tangent solution with nonzero residue denominators produces
legal polynomial data satisfying the complete cleared defect at pole order
one. This theorem deliberately makes no homogeneity assertion. -/
theorem residue_solution_clearing
    (ρ : R →+* K) (Δ₀ : Derivation ℤ R R) (Δ : ι → Derivation ℤ R R)
    (E : ι → Derivation ℤ K K) (f A : R) (w : ι → K)
    (irreducible : Irreducible f)
    (kernel : ∀ p, ρ p = 0 ↔ f ∣ p)
    (g₀_ne : ρ (Δ₀ f) ≠ 0)
    (mixed : ∀ i, Δ i (Δ₀ f) = Δ₀ (Δ i f))
    (compatible : ∀ i p, E i (ρ p) =
      ρ (Δ i p) - ρ (Δ i f) / ρ (Δ₀ f) * ρ (Δ₀ p))
    (representatives : ∃ d : R, ∃ n : ι → R,
      ρ d ≠ 0 ∧ ∀ i, ρ (n i) = ρ d * w i)
    (equation :
      (ρ (Δ₀ A) * ρ (Δ₀ f) - ρ A * ρ (Δ₀ (Δ₀ f))) / (ρ (Δ₀ f))^2 +
        ∑ i, (E i (w i) - w i * E i (ρ (Δ₀ f)) / ρ (Δ₀ f)) = 0) :
    ∃ D N₀ : R, ∃ N : ι → R, ∃ Q : R,
      D ≠ 0 ∧ IsRelPrime f D ∧
      (N₀ * Δ₀ f + ∑ i, N i * Δ i f = A * D) ∧
      (residueDivNum Δ₀ Δ D N₀ N = f * Q) ∧
      A * D^2 - D * (N₀ * Δ₀ f + ∑ i, N i * Δ i f) +
        f * residueDivNum Δ₀ Δ D N₀ N = f^2 * Q := by
  obtain ⟨d, n, hd, hn⟩ := representatives
  let D := Δ₀ f * d
  let N₀ := A * d - ∑ i, Δ i f * n i
  let N : ι → R := fun i => Δ₀ f * n i
  have hD : ρ D ≠ 0 := by
    dsimp [D]
    rw [map_mul]
    exact mul_ne_zero g₀_ne hd
  have hN (i : ι) : ρ (N i) = ρ D * w i := by
    dsimp [D, N]
    rw [map_mul, hn i, map_mul]
    ring
  have hnormal : N₀ * Δ₀ f + ∑ i, N i * Δ i f = A * D :=
    cleared_normal_source A d (Δ₀ f) (fun i => Δ i f) n
  have hdiv := residue_divergence_identity ρ Δ₀ Δ E A D N₀ (Δ₀ f)
    N (fun i => Δ i f) w g₀_ne mixed compatible hN hnormal
  rw [equation, mul_zero] at hdiv
  obtain ⟨Q, hQ⟩ := (kernel (residueDivNum Δ₀ Δ D N₀ N)).mp hdiv
  have hlegal := legal_of_residue_ne_zero ρ f D irreducible kernel hD
  refine ⟨D, N₀, N, Q, hlegal.1, hlegal.2, hnormal, hQ, ?_⟩
  rw [hnormal, hQ]
  ring

end Clearing

end HoldoutConstruction

#print axioms HoldoutConstruction.residue_common_representatives
#print axioms HoldoutConstruction.residue_fractionMap_kernel
#print axioms HoldoutConstruction.cleared_normal_source
#print axioms HoldoutConstruction.legal_of_residue_ne_zero
#print axioms HoldoutConstruction.residue_divergence_identity
#print axioms HoldoutConstruction.residue_solution_clearing
end
end
