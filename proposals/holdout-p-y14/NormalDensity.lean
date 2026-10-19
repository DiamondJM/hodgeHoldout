import Mathlib.Tactic.LinearCombination
import Proposal.Piola

/- Source component: NormalDensity -/
section
/-!
The coefficient of the normal derivative of a residue density is polynomial
along a polynomial curve. Only the first normal vector is required. The
identities below are algebraic construction lemmas, not a certificate.
-/

noncomputable section

namespace HoldoutConstruction

open scoped BigOperators

section MatrixColumn

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_updateCol_inverse (M N : Matrix ι ι R) (hMN : M*N = 1)
    (i : ι) (v : ι → R) :
    (M.updateCol i v).det = M.det * ∑ j, N i j * v j := by
  have hcol : v = fun j => ∑ k, (∑ l, N k l * v l) * M j k := by
    have hh := Matrix.mulVec_mulVec v M N
    rw [hMN, Matrix.one_mulVec] at hh
    ext j
    simpa only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm] using
      (congrFun hh j).symm
  conv_lhs => rw [hcol]
  simpa only [smul_eq_mul, mul_comm] using
    (Matrix.det_updateCol_sum M i (fun k => ∑ l, N k l * v l))

end MatrixColumn

section NormalMatrix

variable {K : Type*} [Field K] {n : ℕ}

def tangentInverse (N : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (g : Fin (n+1) → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => N i.succ j.succ - (N i.succ 0/g 0)*g j.succ

theorem inverse_normal_row
    (M N : Matrix (Fin (n+1)) (Fin (n+1)) K) (g : Fin (n+1) → K)
    (hMN : M*N = 1)
    (hgM : ∀ j, (∑ k, g k*M k j) = if j=0 then 1 else 0) :
    ∀ j, N 0 j = g j := by
  have hh := Matrix.vecMul_vecMul g M N
  rw [hMN, Matrix.vecMul_one] at hh
  have hrow : Matrix.vecMul g M = Pi.single 0 1 := by
    funext j
    simpa only [Matrix.vecMul, dotProduct, Pi.single_apply] using hgM j
  rw [hrow] at hh
  intro j
  have hj := congrFun hh j
  simpa [Matrix.vecMul, dotProduct, Pi.single_apply] using hj

theorem normal_matrix_determinant
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (g : Fin (n+1) → K)
    (hgM : ∀ j, (∑ k, g k*M k j) = if j=0 then 1 else 0) :
    (M.submatrix Fin.succ Fin.succ).det = g 0*M.det := by
  have h := Matrix.det_updateRow_sum M 0 g
  have hrow : (∑ k, g k • M k) = Pi.single 0 1 := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      using hgM j
  rw [hrow] at h
  have hd : (M.updateRow 0 (Pi.single 0 1)).det =
      (M.submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [Matrix.updateRow, Function.update, Matrix.submatrix, Fin.succ_ne_zero]
  rw [hd] at h
  exact h

theorem normal_inverse_tail_product
    (M N : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (g ψ : Fin (n+1) → K) (hMN : M*N = 1)
    (hN : ∀ j, N 0 j = g j) (hM : ∀ j, M j 0 = ψ j) (k : Fin (n+1)) :
    (∑ i : Fin n, M k i.succ * N i.succ 0) =
      (if k=0 then 1 else 0) - ψ k*g 0 := by
  have h := congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) K => A k 0) hMN
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, hN, hM, Matrix.one_apply] at h
  linear_combination h

theorem tangentInverse_right
    (M N : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (g ψ : Fin (n+1) → K) (hg : g 0 ≠ 0) (hMN : M*N = 1)
    (hN : ∀ j, N 0 j = g j) (hM : ∀ j, M j 0 = ψ j) :
    M.submatrix Fin.succ Fin.succ * tangentInverse N g = 1 := by
  ext j k
  have h1 := congrArg
    (fun A : Matrix (Fin (n+1)) (Fin (n+1)) K => A j.succ k.succ) hMN
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, hN, hM, Matrix.one_apply] at h1
  have h0 := normal_inverse_tail_product M N g ψ hMN hN hM j.succ
  simp only [Fin.succ_ne_zero, ↓reduceIte, zero_sub] at h0
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, tangentInverse,
    mul_sub, Finset.sum_sub_distrib, Matrix.one_apply]
  have hs : (∑ i : Fin n, M j.succ i.succ * (N i.succ 0/g 0*g k.succ)) =
      (∑ i : Fin n, M j.succ i.succ*N i.succ 0) * (g k.succ/g 0) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs, h0]
  simp only [Fin.succ_inj] at h1
  field_simp
  linear_combination h1

theorem tangentInverse_left
    (M N : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (g : Fin (n+1) → K) (hg : g 0 ≠ 0) (hNM : N*M = 1)
    (hN : ∀ j, N 0 j = g j) :
    tangentInverse N g * M.submatrix Fin.succ Fin.succ = 1 := by
  ext i k
  have h1 := congrArg
    (fun A : Matrix (Fin (n+1)) (Fin (n+1)) K => A i.succ k.succ) hNM
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] at h1
  have h0 := congrArg
    (fun A : Matrix (Fin (n+1)) (Fin (n+1)) K => A 0 k.succ) hNM
  simp [Matrix.mul_apply, Fin.sum_univ_succ, hN, Matrix.one_apply] at h0
  simp only [Ne.symm (Fin.succ_ne_zero k), ↓reduceIte] at h0
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, tangentInverse,
    sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, Matrix.one_apply]
  simp only [Fin.succ_inj] at h1
  field_simp
  linear_combination g 0*h1 - N i.succ 0*h0

theorem split_normal_row
    (N : Matrix (Fin (n+1)) (Fin (n+1)) K) (g : Fin (n+1) → K)
    (hg : g 0 ≠ 0) (a : Fin n → Fin (n+1) → K) (i : Fin n) :
    (∑ j, N i.succ j*a i j) =
      (∑ j : Fin n, tangentInverse N g i j*a i j.succ) +
      (N i.succ 0/g 0)*(∑ j, g j*a i j) := by
  simp only [Fin.sum_univ_succ, tangentInverse, sub_mul, mul_assoc,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp
  ring

theorem normal_trace_correction
    (M N : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (g ψ : Fin (n+1) → K) (H : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (hg : g 0 ≠ 0) (hMN : M*N = 1)
    (hN : ∀ j, N 0 j = g j) (hM : ∀ j, M j 0 = ψ j)
    (a : Fin n → Fin (n+1) → K)
    (ha : ∀ i, (∑ j, g j*a i j) = -∑ j, ∑ k, H j k*M k i.succ*ψ j) :
    (∑ i : Fin n, ∑ j, N i.succ j*a i j) =
      (∑ j : Fin n, ∑ i, tangentInverse N g i j*a i j.succ) +
      (∑ j, ∑ k, ψ j*H j k*ψ k) - (∑ j, ψ j*H j 0)/g 0 := by
  have hc : (∑ i : Fin n, (N i.succ 0/g 0)*
        (∑ j, ∑ k, H j k*M k i.succ*ψ j)) =
      (∑ j, ψ j*H j 0)/g 0 - (∑ j, ∑ k, ψ j*H j k*ψ k) := by
    have hr : (∑ i : Fin n, (N i.succ 0/g 0)*
        (∑ j, ∑ k, H j k*M k i.succ*ψ j)) =
        ∑ j, ∑ k, (ψ j*H j k/g 0)*(∑ i : Fin n, M k i.succ*N i.succ 0) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hr]
    simp_rw [normal_inverse_tail_product M N g ψ hMN hN hM]
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hd : (∑ j, ∑ k, (ψ j*H j k/g 0)*(if k=0 then 1 else 0)) =
        (∑ j, ψ j*H j 0)/g 0 := by
      simp [mul_ite, div_eq_mul_inv, Finset.sum_mul]
    have hq : (∑ j, ∑ k, (ψ j*H j k/g 0)*(ψ k*g 0)) =
        ∑ j, ∑ k, ψ j*H j k*ψ k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      field_simp
    rw [hd, hq]
  calc
    _ = (∑ i : Fin n, ∑ j : Fin n, tangentInverse N g i j*a i j.succ) +
        ∑ i : Fin n, (N i.succ 0/g 0)*(∑ j, g j*a i j) := by
      simp_rw [split_normal_row N g hg a]
      rw [Finset.sum_add_distrib]
    _ = (∑ j : Fin n, ∑ i, tangentInverse N g i j*a i j.succ) -
        ∑ i : Fin n, (N i.succ 0/g 0)*(∑ j, ∑ k, H j k*M k i.succ*ψ j) := by
      simp_rw [ha, mul_neg, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      ring
    _ = _ := by rw [hc]; ring

/-- Polynomial determinant expression for the potentially rational normal
divergence term. -/
theorem normal_density_determinants
    (M N : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (g ψ : Fin (n+1) → K) (H : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (hg : g 0 ≠ 0) (hMN : M*N = 1)
    (hN : ∀ j, N 0 j = g j) (hM : ∀ j, M j 0 = ψ j)
    (a : Fin n → Fin (n+1) → K)
    (ha : ∀ i, (∑ j, g j*a i j) = -∑ j, ∑ k, H j k*M k i.succ*ψ j) :
    M.det*(∑ j : Fin n, ∑ i, tangentInverse N g i j*a i j.succ) -
        M.det*(∑ j, ψ j*H j 0)/g 0 =
      (∑ i : Fin n, (M.updateCol i.succ (a i)).det) -
        M.det*(∑ j, ∑ k, ψ j*H j k*ψ k) := by
  simp_rw [det_updateCol_inverse M N hMN]
  rw [← Finset.mul_sum, normal_trace_correction M N g ψ H hg hMN hN hM a ha]
  ring

end NormalMatrix

section NormalDerivatives

variable {K : Type*} [Field K] {n : ℕ}

theorem normal_vector_derivative
    (D : Fin n → Derivation ℤ K K)
    (M H : Matrix (Fin (n+1)) (Fin (n+1)) K) (g ψ : Fin (n+1) → K)
    (hψ : (∑ j, g j*ψ j) = 1)
    (hg : ∀ i j, D i (g j) = ∑ k, H j k*M k i.succ) :
    ∀ i, (∑ j, g j*D i (ψ j)) = -∑ j, ∑ k, H j k*M k i.succ*ψ j := by
  intro i
  have h := congrArg (D i) hψ
  simp only [map_sum, Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul,
    Finset.sum_add_distrib] at h
  have hs : (∑ j, ψ j*D i (g j)) = ∑ j, ∑ k, H j k*M k i.succ*ψ j := by
    simp_rw [hg, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs] at h
  linear_combination h

theorem residue_normal_divergence
    (E : Fin n → Derivation ℤ K K) (g ψ b : Fin (n+1) → K)
    (H : Matrix (Fin (n+1)) (Fin (n+1)) K) (B : K)
    (hg : g 0 ≠ 0) (hψ : (∑ j, g j*ψ j) = 1)
    (hb : ∀ j, E j B = b j.succ - (g j.succ/g 0)*b 0)
    (hH : ∀ j, E j (g 0) = H j.succ 0 - (g j.succ/g 0)*H 0 0) :
    (b 0/g 0 - B*H 0 0/(g 0)^2) +
        residueDivergence E (g 0) (fun j => B*ψ j.succ) =
      (∑ j, ψ j*b j) + B*((∑ j : Fin n, E j (ψ j.succ)) -
        (∑ j, ψ j*H j 0)/g 0) := by
  have hd : fieldDivergence E (fun j => B*ψ j.succ) =
      B*(∑ j : Fin n, E j (ψ j.succ)) + (∑ j : Fin n, ψ j.succ*b j.succ) -
        (b 0/g 0)*(∑ j : Fin n, ψ j.succ*g j.succ) := by
    have ht : ∀ j, E j (B*ψ j.succ) = B*E j (ψ j.succ) +
        ψ j.succ*b j.succ - (b 0/g 0)*(ψ j.succ*g j.succ) := by
      intro j
      rw [Derivation.leibniz, hb]
      simp only [smul_eq_mul]
      ring
    simp only [fieldDivergence, ht, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  have hv : (∑ j : Fin n, (B*ψ j.succ)*E j (g 0)) =
      B*(∑ j : Fin n, ψ j.succ*H j.succ 0) -
        (B*H 0 0/g 0)*(∑ j : Fin n, ψ j.succ*g j.succ) := by
    have ht : ∀ j, (B*ψ j.succ)*E j (g 0) =
        B*(ψ j.succ*H j.succ 0) - (B*H 0 0/g 0)*(ψ j.succ*g j.succ) := by
      intro j
      rw [hH]
      ring
    simp only [ht, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hn : g 0*ψ 0 + (∑ j : Fin n, ψ j.succ*g j.succ) = 1 := by
    simpa only [Fin.sum_univ_succ, mul_comm] using hψ
  rw [residueDivergence, hd, hv]
  simp only [Fin.sum_univ_succ]
  field_simp
  linear_combination -(b 0*g 0-B*H 0 0)*hn

/-- The right-hand side consists only of polynomial operations in the
curve coordinates, their first normal vector, and parameter derivatives.
It is therefore a polynomial density along the curve parameter. -/
theorem normal_density_formula
    (D E : Fin n → Derivation ℤ K K)
    (M N H : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (g ψ b : Fin (n+1) → K) (B : K)
    (hg0 : g 0 ≠ 0) (hMN : M*N = 1)
    (hN : ∀ j, N 0 j = g j) (hM : ∀ j, M j 0 = ψ j)
    (hψ : (∑ j, g j*ψ j) = 1)
    (hg : ∀ i j, D i (g j) = ∑ k, H j k*M k i.succ)
    (chain : ∀ j x, E j x = ∑ i, tangentInverse N g i j*D i x)
    (hb : ∀ j, E j B = b j.succ - (g j.succ/g 0)*b 0)
    (hH : ∀ j, E j (g 0) = H j.succ 0 - (g j.succ/g 0)*H 0 0) :
    M.det*((b 0/g 0 - B*H 0 0/(g 0)^2) +
        residueDivergence E (g 0) (fun j => B*ψ j.succ)) =
      M.det*(∑ j, ψ j*b j) + B*((∑ i : Fin n,
        (M.updateCol i.succ (fun j => D i (ψ j))).det) -
        M.det*(∑ j, ∑ k, ψ j*H j k*ψ k)) := by
  have ha := normal_vector_derivative D M H g ψ hψ hg
  have hh := normal_density_determinants M N g ψ H hg0 hMN hN hM
    (fun i j => D i (ψ j)) ha
  rw [residue_normal_divergence E g ψ b H B hg0 hψ hb hH]
  simp_rw [chain]
  linear_combination B*hh

end NormalDerivatives

end HoldoutConstruction

#print axioms HoldoutConstruction.normal_matrix_determinant
#print axioms HoldoutConstruction.tangentInverse_right
#print axioms HoldoutConstruction.tangentInverse_left
#print axioms HoldoutConstruction.normal_density_formula
end
end
