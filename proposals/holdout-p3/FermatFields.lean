import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic
import Proposal.HypersurfaceDomain

/- Source component: FermatBase -/
section
/-!
Coordinate-ring interface for the Fermat base of the holdout cover.
Evaluation occurs on the coordinate ring before passage to its fraction
field, so no specialization of a generic rational denominator is assumed.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

variable {R : Type*} [CommRing R]

abbrev FermatBaseRing (R : Type*) [CommRing R] :=
  AdjoinRoot (fermatCurvePolynomial (R := R))

def baseAlpha : FermatBaseRing R :=
  AdjoinRoot.root (fermatCurvePolynomial (R := R))

def baseBeta : FermatBaseRing R :=
  AdjoinRoot.of (fermatCurvePolynomial (R := R)) X

theorem fermat_base_relation : (baseAlpha (R := R))^6 + (baseBeta (R := R))^6 = 1 := by
  have h := AdjoinRoot.eval₂_root (fermatCurvePolynomial (R := R))
  change (X^6+C (X^6-1 : R[X])).eval₂
    (AdjoinRoot.of (fermatCurvePolynomial (R := R))) (baseAlpha (R := R)) = 0 at h
  rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  have hh : (baseAlpha (R := R))^6 + ((baseBeta (R := R))^6-1) = 0 := by
    simpa only [map_sub, map_pow, map_one, baseBeta] using h
  linear_combination hh

def baseEval (a b : R) (h : a^6+b^6=1) : FermatBaseRing R →+* R :=
  AdjoinRoot.lift (f := fermatCurvePolynomial (R := R)) (Polynomial.evalRingHom b) a (by
    change (X^6+C (X^6-1 : R[X])).eval₂ (Polynomial.evalRingHom b) a = 0
    rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    change a^6 + (X^6-1 : R[X]).eval b = 0
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one]
    linear_combination h)

@[simp] theorem baseEval_alpha (a b : R) (h : a^6+b^6=1) :
    baseEval a b h (baseAlpha (R := R)) = a := by
  simp [baseEval, baseAlpha]

@[simp] theorem baseEval_beta (a b : R) (h : a^6+b^6=1) :
    baseEval a b h (baseBeta (R := R)) = b := by
  simp [baseEval, baseBeta]

@[simp] theorem baseEval_coefficient (a b : R) (h : a^6+b^6=1) (r : R) :
    baseEval a b h (algebraMap R (FermatBaseRing R) r) = r := by
  change baseEval a b h (AdjoinRoot.of _ (Polynomial.C r)) = r
  simp [baseEval]

theorem fermat_base_of_injective [IsDomain R] :
    Function.Injective (AdjoinRoot.of (fermatCurvePolynomial (R := R))) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  change (X^6+C (X^6-1 : R[X])).degree ≠ 0
  rw [degree_X_pow_add_C (by decide)]
  norm_num

theorem fermat_base_charZero [IsDomain R] [CharZero R] : CharZero (FermatBaseRing R) :=
  charZero_of_injective_ringHom
    (f := (AdjoinRoot.of (fermatCurvePolynomial (R := R))).comp
      (Polynomial.C : R →+* R[X]))
    ((fermat_base_of_injective (R := R)).comp Polynomial.C_injective)

theorem baseAlpha_ne_zero [Nontrivial R] : baseAlpha (R := R) ≠ 0 := by
  intro h
  have hh := congrArg (baseEval (1:R) 0 (by simp)) h
  simp at hh

theorem baseBeta_ne_zero [Nontrivial R] : baseBeta (R := R) ≠ 0 := by
  intro h
  have hh := congrArg (baseEval (0:R) 1 (by simp)) h
  simp at hh

end HoldoutConstruction

#print axioms HoldoutConstruction.fermat_base_relation
#print axioms HoldoutConstruction.fermat_base_of_injective
#print axioms HoldoutConstruction.baseAlpha_ne_zero
end
end

/- Source component: DensePolynomialMap -/
section
/-!
An elementary dense-evaluation criterion for injectivity of a polynomial
map. It uses polynomial function extensionality over an infinite field,
without a geometric dominance or dimension theorem. Prepared with OpenAI
ChatGPT assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

variable {K Q σ : Type*} [Field K] [Infinite K] [CommRing Q]

/-- If every point outside one nonzero polynomial has a compatible
evaluation of the target ring, the polynomial map is injective. -/
theorem polynomialMap_injective_of_dense_evaluations
    (φ : MvPolynomial σ K →+* Q) (cutoff : MvPolynomial σ K)
    (cutoff_ne : cutoff ≠ 0)
    (lift : ∀ x : σ → K, MvPolynomial.eval x cutoff ≠ 0 →
      ∃ e : Q →+* K, ∀ p, e (φ p) = MvPolynomial.eval x p) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hprod : cutoff * p = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [MvPolynomial.eval_mul, map_zero]
    by_cases hx : MvPolynomial.eval x cutoff = 0
    · rw [hx, zero_mul]
    · obtain ⟨e, he⟩ := lift x hx
      have he0 : MvPolynomial.eval x p = 0 := by
        rw [← he p, hp, map_zero]
      rw [he0, mul_zero]
  exact (mul_eq_zero.mp hprod).resolve_left cutoff_ne

end HoldoutConstruction

#print axioms HoldoutConstruction.polynomialMap_injective_of_dense_evaluations
end
end

/- Source component: FermatConeEmbedding -/
section
/-!
Injectivity of the physical coefficient map into the Fermat common-cover
coefficient ring. The proof lifts evaluations with nonzero sixth-power sum,
then uses a proved dense-evaluation criterion. Prepared with OpenAI ChatGPT
assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

section CoefficientMap

variable {K : Type*} [CommRing K]

/-- Physical coefficient order is X1,X2,Y0,Y1,Y2; the cover coefficient
order is X1,X2,y,T. -/
def physicalCoverCoefficientMap :
    MvPolynomial (Fin 5) K →+* MvPolynomial (Fin 4) (FermatBaseRing K) :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (algebraMap K (FermatBaseRing K)))
    ![MvPolynomial.X 0, MvPolynomial.X 1,
      MvPolynomial.C (baseAlpha (R := K)) * MvPolynomial.X 3,
      MvPolynomial.X 2,
      MvPolynomial.C (baseBeta (R := K)) * MvPolynomial.X 3]

end CoefficientMap

section Injectivity

variable {K : Type*} [Field K] [Infinite K] [IsAlgClosed K]

/-- The map from the physical coefficient polynomial ring is injective.
The construction takes roots only at evaluations with nonzero sixth-power
sum; no generic rational denominator is specialized. -/
theorem physicalCoverCoefficientMap_injective :
    Function.Injective (physicalCoverCoefficientMap (K := K)) := by
  let cutoff : MvPolynomial (Fin 5) K := MvPolynomial.X 2^6 + MvPolynomial.X 4^6
  have hcutoff : cutoff ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval ![0, 0, 1, 0, 0]) h
    simp [cutoff] at he
  apply polynomialMap_injective_of_dense_evaluations
    (physicalCoverCoefficientMap (K := K)) cutoff hcutoff
  intro x hx
  have hc : x 2^6 + x 4^6 ≠ 0 := by simpa [cutoff] using hx
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (x 2^6 + x 4^6) (show 0 < 6 by decide)
  have ht0 : t ≠ 0 := by
    intro h
    apply hc
    simpa [h] using ht.symm
  have hab : (x 2 / t)^6 + (x 4 / t)^6 = 1 := by
    rw [div_pow, div_pow, ← add_div, ht, div_self hc]
  let e : MvPolynomial (Fin 4) (FermatBaseRing K) →+* K :=
    MvPolynomial.eval₂Hom (baseEval (x 2 / t) (x 4 / t) hab)
      ![x 0, x 1, x 3, t]
  have he : e.comp (physicalCoverCoefficientMap (K := K)) = MvPolynomial.eval x := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e, physicalCoverCoefficientMap]
    · intro i
      fin_cases i <;>
        simp [e, physicalCoverCoefficientMap, div_mul_cancel₀ _ ht0]
  refine ⟨e, ?_⟩
  intro p
  exact RingHom.congr_fun he p

end Injectivity

end HoldoutConstruction

#print axioms HoldoutConstruction.physicalCoverCoefficientMap_injective
end
end

/- Source component: FermatBaseLift -/
section
/-!
Universal evaluations and sixth-root scaling on the Fermat coefficient
curve. The scaling is an actual ring equivalence, so it can be extended
to the coefficient fraction field without choosing a branch. Prepared
with OpenAI ChatGPT assistance for a contribution through GitHub account
fqlx, using the Lean/mathlib AdjoinRoot construction.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

section Lift

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The universal Fermat-curve evaluation into a possibly different ring. -/
def fermatBaseLift (φ : R →+* S) (a b : S) (h : a^6+b^6=1) :
    FermatBaseRing R →+* S :=
  AdjoinRoot.lift (f := fermatCurvePolynomial (R := R))
    (Polynomial.eval₂RingHom φ b) a (by
      change (X^6+C (X^6-1 : R[X])).eval₂
        (Polynomial.eval₂RingHom φ b) a = 0
      rw [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      change a^6 + (X^6-1 : R[X]).eval₂ φ b = 0
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_one]
      linear_combination h)

@[simp] theorem fermatBaseLift_alpha (φ : R →+* S)
    (a b : S) (h : a^6+b^6=1) :
    fermatBaseLift φ a b h (baseAlpha (R := R)) = a := by
  simp [fermatBaseLift, baseAlpha]

@[simp] theorem fermatBaseLift_beta (φ : R →+* S)
    (a b : S) (h : a^6+b^6=1) :
    fermatBaseLift φ a b h (baseBeta (R := R)) = b := by
  simp [fermatBaseLift, baseBeta]

@[simp] theorem fermatBaseLift_coefficient (φ : R →+* S)
    (a b : S) (h : a^6+b^6=1) (r : R) :
    fermatBaseLift φ a b h (algebraMap R (FermatBaseRing R) r) = φ r := by
  change fermatBaseLift φ a b h (AdjoinRoot.of _ (Polynomial.C r)) = φ r
  simp [fermatBaseLift]

/-- Constants and the two displayed coordinates determine a map out of
the Fermat coordinate ring. -/
theorem fermatBase_ringHom_ext {f g : FermatBaseRing R →+* S}
    (hC : ∀ r : R,
      f (algebraMap R (FermatBaseRing R) r) =
        g (algebraMap R (FermatBaseRing R) r))
    (hA : f (baseAlpha (R := R)) = g (baseAlpha (R := R)))
    (hB : f (baseBeta (R := R)) = g (baseBeta (R := R))) : f = g := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      exact hC r
    · exact hB
  · exact hA

end Lift

section Scaling

variable {K : Type*} [Field K]

/-- Multiplication of both Fermat coordinates by a sixth root of unity. -/
def fermatBaseScale (z : K) (hz : z^6=1) :
    FermatBaseRing K →+* FermatBaseRing K :=
  fermatBaseLift (algebraMap K (FermatBaseRing K))
    (algebraMap K (FermatBaseRing K) z * baseAlpha)
    (algebraMap K (FermatBaseRing K) z * baseBeta) (by
      calc
        _ = (algebraMap K (FermatBaseRing K) z)^6 *
            ((baseAlpha (R := K))^6+(baseBeta (R := K))^6) := by ring
        _ = 1 := by rw [← map_pow, hz, map_one, fermat_base_relation, one_mul])

@[simp] theorem fermatBaseScale_alpha (z : K) (hz : z^6=1) :
    fermatBaseScale z hz (baseAlpha (R := K)) =
      algebraMap K (FermatBaseRing K) z * baseAlpha := by
  simp [fermatBaseScale]

@[simp] theorem fermatBaseScale_beta (z : K) (hz : z^6=1) :
    fermatBaseScale z hz (baseBeta (R := K)) =
      algebraMap K (FermatBaseRing K) z * baseBeta := by
  simp [fermatBaseScale]

@[simp] theorem fermatBaseScale_coefficient (z : K) (hz : z^6=1) (r : K) :
    fermatBaseScale z hz (algebraMap K (FermatBaseRing K) r) =
      algebraMap K (FermatBaseRing K) r := by
  simp [fermatBaseScale]

/-- The curve scaling has an explicit inverse and hence is injective. -/
def fermatBaseScaleEquiv (z : K) (hz : z^6=1) (hz0 : z ≠ 0) :
    FermatBaseRing K ≃+* FermatBaseRing K :=
  RingEquiv.ofRingHom (fermatBaseScale z hz)
    (fermatBaseScale z⁻¹ (by rw [inv_pow, hz, inv_one]))
    (by
      apply fermatBase_ringHom_ext
      · intro r; simp
      · simp only [RingHom.comp_apply, RingHom.id_apply, fermatBaseScale_alpha,
          map_mul, fermatBaseScale_coefficient]
        simp [← mul_assoc, ← map_mul, hz0]
      · simp only [RingHom.comp_apply, RingHom.id_apply, fermatBaseScale_beta,
          map_mul, fermatBaseScale_coefficient]
        simp [← mul_assoc, ← map_mul, hz0])
    (by
      apply fermatBase_ringHom_ext
      · intro r; simp
      · simp only [RingHom.comp_apply, RingHom.id_apply, fermatBaseScale_alpha,
          map_mul, fermatBaseScale_coefficient]
        simp [← mul_assoc, ← map_mul, hz0]
      · simp only [RingHom.comp_apply, RingHom.id_apply, fermatBaseScale_beta,
          map_mul, fermatBaseScale_coefficient]
        simp [← mul_assoc, ← map_mul, hz0])

end Scaling

end HoldoutConstruction

#print axioms HoldoutConstruction.fermatBaseScaleEquiv
#print axioms HoldoutConstruction.fermatBase_ringHom_ext
end
end

/- Source component: MvPolynomialScale -/
section
/-!
An explicit invertible scaling of the T coordinate in the four-variable
common-cover coefficient ring. Prepared with OpenAI ChatGPT assistance
for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

section ScalingMap

variable {R : Type*} [CommRing R]

def scaleLastVariable (c : R) :
    MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
      MvPolynomial.C c * MvPolynomial.X 3]

@[simp] theorem scaleLastVariable_C (c r : R) :
    scaleLastVariable c (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [scaleLastVariable]

@[simp] theorem scaleLastVariable_X (c : R) (i : Fin 4) :
    scaleLastVariable c (MvPolynomial.X i) =
      ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
        MvPolynomial.C c * MvPolynomial.X 3] i := by
  simp [scaleLastVariable]

end ScalingMap

section ScalingEquiv

variable {K : Type*} [Field K]

def scaleLastVariableEquiv (c : K) (hc : c ≠ 0) :
    MvPolynomial (Fin 4) K ≃+* MvPolynomial (Fin 4) K :=
  RingEquiv.ofRingHom (scaleLastVariable c) (scaleLastVariable c⁻¹)
    (by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro i
        fin_cases i <;>
          simp [scaleLastVariable, -MvPolynomial.eval₂Hom_C_eq_bind₁]
        simp [← mul_assoc, ← map_mul, hc])
    (by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro i
        fin_cases i <;>
          simp [scaleLastVariable, -MvPolynomial.eval₂Hom_C_eq_bind₁]
        simp [← mul_assoc, ← map_mul, hc])

@[simp] theorem scaleLastVariableEquiv_apply (c : K) (hc : c ≠ 0)
    (p : MvPolynomial (Fin 4) K) :
    scaleLastVariableEquiv c hc p = scaleLastVariable c p := rfl

end ScalingEquiv

end HoldoutConstruction

#print axioms HoldoutConstruction.scaleLastVariableEquiv
end
end
