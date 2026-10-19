import Proposal.NormalDensity

/- Source component: PolynomialFamily -/
section
/-!
A generic algebraic residue primitive from a polynomial family with a
nonzero evaluation determinant. This file states every differential and
polynomiality hypothesis explicitly; it does not claim those hypotheses
for the holdout until the incidence construction supplies them.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

section SubringDeterminant

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem determinant_mem_subring (S : Subring R) (M : Matrix ι ι R)
    (hM : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  let M' : Matrix ι ι S := fun i j => ⟨M i j, hM i j⟩
  have hmap : S.subtype.mapMatrix M' = M := rfl
  rw [← hmap, ← S.subtype.map_det]
  exact (M'.det).property

theorem determinant_updateCol_mem_subring (S : Subring R) (M : Matrix ι ι R)
    (hM : ∀ i j, M i j ∈ S) (i : ι) (v : ι → R) (hv : ∀ j, v j ∈ S) :
    (M.updateCol i v).det ∈ S := by
  apply determinant_mem_subring
  intro j k
  by_cases h : k=i
  · subst k; simpa using hv j
  · simpa [Matrix.updateCol, h] using hM j k

end SubringDeterminant

section PolynomialFamily

variable {K R : Type*} [Field K] [CharZero K] [CommRing R] {n : ℕ}

/-- A polynomial density along the rational parameter gives a residue
solution. The coefficient ring need not itself be a rational function
field; algebraic coefficients constant along the parameter are allowed. -/
theorem residue_solution_of_polynomial_family
    (D E : Fin n → Derivation ℤ K K)
    (M N H : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (g ψ b : Fin (n+1) → K) (B : K)
    (φ : R →+* K) (t : K) (tIndex : Fin n)
    (hconst : ∀ a, D tIndex (φ a) = 0) (ht : D tIndex t = 1)
    (hg0 : g 0 ≠ 0) (hdet : M.det ≠ 0)
    (hMN : M*N = 1) (hNM : N*M = 1)
    (hN : ∀ j, N 0 j = g j) (hM : ∀ j, M j 0 = ψ j)
    (hψ : (∑ j, g j*ψ j) = 1)
    (hg : ∀ i j, D i (g j) = ∑ k, H j k*M k i.succ)
    (chain : ∀ j x, E j x = ∑ i, tangentInverse N g i j*D i x)
    (mixed : ∀ (i j k : Fin n), D k (M j.succ i.succ) = D i (M j.succ k.succ))
    (hb : ∀ j, E j B = b j.succ - (g j.succ/g 0)*b 0)
    (hH : ∀ j, E j (g 0) = H j.succ 0 - (g j.succ/g 0)*H 0 0)
    (hpolyM : ∀ i j, M i j ∈ (Polynomial.eval₂RingHom φ t).range)
    (hpolyH : ∀ i j, H i j ∈ (Polynomial.eval₂RingHom φ t).range)
    (hpolyψ : ∀ j, ψ j ∈ (Polynomial.eval₂RingHom φ t).range)
    (hpolyb : ∀ j, b j ∈ (Polynomial.eval₂RingHom φ t).range)
    (hpolyB : B ∈ (Polynomial.eval₂RingHom φ t).range)
    (hpolyDψ : ∀ i j, D i (ψ j) ∈ (Polynomial.eval₂RingHom φ t).range) :
    ∃ w : Fin n → K,
      residueDivergence E (g 0) w = -(b 0/g 0-B*H 0 0/(g 0)^2) := by
  let S : Subring K := (Polynomial.eval₂RingHom φ t).range
  let p : K := M.det*(∑ j, ψ j*b j) + B*((∑ i : Fin n,
      (M.updateCol i.succ (fun j => D i (ψ j))).det) -
      M.det*(∑ j, ∑ k, ψ j*H j k*ψ k))
  have hp : p ∈ S := by
    have hJ : M.det ∈ S := determinant_mem_subring S M hpolyM
    apply S.add_mem
    · exact S.mul_mem hJ (S.sum_mem fun j _ => S.mul_mem (hpolyψ j) (hpolyb j))
    · apply S.mul_mem hpolyB
      apply S.sub_mem
      · apply S.sum_mem
        intro i _
        exact determinant_updateCol_mem_subring S M hpolyM i.succ
          (fun j => D i (ψ j)) (hpolyDψ i)
      · apply S.mul_mem hJ
        apply S.sum_mem
        intro j _
        apply S.sum_mem
        intro k _
        exact S.mul_mem (S.mul_mem (hpolyψ j) (hpolyH j k)) (hpolyψ k)
  obtain ⟨P, hP⟩ := hp
  obtain ⟨h, hh⟩ := exists_polynomial_antiderivative (D tIndex) φ hconst t ht P
  change P.eval₂ φ t = p at hP
  rw [hP] at hh
  have hgM : ∀ j, (∑ k, g k*M k j) = if j=0 then 1 else 0 := by
    intro j
    have h := congrArg
      (fun A : Matrix (Fin (n+1)) (Fin (n+1)) K => A 0 j) hNM
    simpa only [Matrix.mul_apply, hN, Matrix.one_apply, eq_comm] using h
  have hd := normal_matrix_determinant M g hgM
  have hpformula : p = M.det*((b 0/g 0 - B*H 0 0/(g 0)^2) +
      residueDivergence E (g 0) (fun j => B*ψ j.succ)) :=
    (normal_density_formula D E M N H g ψ b B hg0 hMN hN hM hψ hg chain hb hH).symm
  exact residue_solution_of_antiderivative D E
    (M.submatrix Fin.succ Fin.succ) (tangentInverse N g)
    (g 0) M.det hg0 hdet hd
    (tangentInverse_right M N g ψ hg0 hMN hN hM)
    (tangentInverse_left M N g hg0 hNM hN) chain mixed
    (fun j => B*ψ j.succ) (b 0/g 0 - B*H 0 0/(g 0)^2) p h tIndex hpformula hh

end PolynomialFamily

end HoldoutConstruction

#print axioms HoldoutConstruction.residue_solution_of_polynomial_family
end
end
