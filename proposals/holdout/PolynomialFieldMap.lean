import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions

/- Source component: PolynomialFieldMap -/
section
/-!
An elementary injectivity criterion for an anchored polynomial family.
Independent endpoint parameters remain independent after polynomial
deformation when one distinguished coordinate is a nonzero multiple of
the curve parameter.
-/

noncomputable section

namespace HoldoutConstruction

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]

omit [IsDomain S] in
theorem polynomial_family_constantCoeff
    (f : R →+* Polynomial S) (k : S) (p : Polynomial R) :
    Polynomial.constantCoeff (p.eval₂ f (Polynomial.C k*Polynomial.X)) =
      (Polynomial.constantCoeff.comp f) (p.coeff 0) := by
  have h : Polynomial.constantCoeff.comp
        (Polynomial.eval₂RingHom f (Polynomial.C k*Polynomial.X)) =
      (Polynomial.constantCoeff.comp f).comp Polynomial.constantCoeff := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · simp
  exact congrArg (fun h : Polynomial R →+* S => h p) h

theorem polynomial_family_injective
    (f : R →+* Polynomial S)
    (hf : Function.Injective (Polynomial.constantCoeff.comp f))
    (k : S) (hk : k ≠ 0) :
    Function.Injective (Polynomial.eval₂RingHom f (Polynomial.C k*Polynomial.X)) := by
  let θ := Polynomial.eval₂RingHom f (Polynomial.C k*Polynomial.X)
  have hX : θ Polynomial.X ≠ 0 := by
    change Polynomial.eval₂ f (Polynomial.C k*Polynomial.X) Polynomial.X ≠ 0
    rw [Polynomial.eval₂_X]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hk) Polynomial.X_ne_zero
  have hker : ∀ p : Polynomial R, p ≠ 0 → θ p ≠ 0 := by
    intro p
    refine Polynomial.recOnHorner p (by simp) ?_ ?_
    · intro p a hp0 ha _ _ heq
      have hc := congrArg Polynomial.constantCoeff heq
      change Polynomial.constantCoeff
        ((p+Polynomial.C a).eval₂ f (Polynomial.C k*Polynomial.X)) = 0 at hc
      rw [polynomial_family_constantCoeff] at hc
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_zero, hp0, zero_add] at hc
      exact ha (hf (hc.trans (map_zero (Polynomial.constantCoeff.comp f)).symm))
    · intro p hp ih _ heq
      exact mul_ne_zero (ih hp) hX (by simpa only [map_mul] using heq)
  intro p q hpq
  by_contra h
  exact hker (p-q) (sub_ne_zero.mpr h) (by rw [map_sub, hpq, sub_self])

end HoldoutConstruction

#print axioms HoldoutConstruction.polynomial_family_injective
end
end
