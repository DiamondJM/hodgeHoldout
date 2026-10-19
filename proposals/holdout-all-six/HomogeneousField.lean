import Mathlib.Algebra.Ring.GeomSum
import Proposal.HomogeneousIdeal

/- Source component: HomogeneousField -/
section
/-!
Finite denominator replacement and homogeneous projection of rational fields.
These are intermediate lemmas, not a HasCertificate theorem.
-/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial
open scoped BigOperators

variable {R σ : Type*} [CommRing R] [Fintype σ]

def polynomialDirectional (p : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := ∑ i, N i * pderiv i p

def polynomialDivergence (N : σ → MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i, pderiv i (N i)

def polynomialDivNum (D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    MvPolynomial σ R := D*polynomialDivergence N - polynomialDirectional D N

theorem polynomialDirectional_mul (p q : MvPolynomial σ R)
    (N : σ → MvPolynomial σ R) :
    polynomialDirectional (p*q) N =
      p*polynomialDirectional q N + q*polynomialDirectional p N := by
  simp only [polynomialDirectional, pderiv_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  conv_rhs => rw [add_comm]
  apply congrArg₂ (·+·) <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem polynomialDirectional_scale (p S : MvPolynomial σ R)
    (N : σ → MvPolynomial σ R) :
    polynomialDirectional p (fun i => S*N i) = S*polynomialDirectional p N := by
  simp only [polynomialDirectional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem polynomialDivergence_scale (S : MvPolynomial σ R)
    (N : σ → MvPolynomial σ R) :
    polynomialDivergence (fun i => S*N i) =
      polynomialDirectional S N + S*polynomialDivergence N := by
  simp only [polynomialDivergence, polynomialDirectional, pderiv_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact identity behind finite geometric-series replacement of a
denominator. The original divergence may be a nonzero multiple of `F`. -/
theorem denominator_replacement_divergence
    (D S H U : MvPolynomial σ R) (N : σ → MvPolynomial σ R)
    (hDS : D*S = H-U) :
    D^2*polynomialDivNum H (fun i => S*N i) =
      H*(H-U)*polynomialDivNum D N -
        D*(H*polynomialDirectional U N - U*polynomialDirectional H N) := by
  have hd := congrArg (fun p => polynomialDirectional p N) hDS
  rw [polynomialDirectional_mul] at hd
  simp only [polynomialDirectional, map_sub,
    mul_sub, Finset.sum_sub_distrib] at hd
  change D*polynomialDirectional S N + S*polynomialDirectional D N =
    polynomialDirectional H N - polynomialDirectional U N at hd
  simp only [polynomialDivNum, polynomialDivergence_scale, polynomialDirectional_scale]
  linear_combination D*H*hd +
    (D*polynomialDivergence N - polynomialDirectional D N)*H*hDS -
    D*polynomialDirectional H N*hDS

theorem order_polynomialDirectional {n : ℕ} {p : MvPolynomial σ R}
    (hp : HasOrder n p) (N : σ → MvPolynomial σ R) :
    HasOrder (n-1) (polynomialDirectional p N) := by
  apply HasOrder.sum
  intro i _
  simpa using (hasOrder_zero_degree (N i)).mul (hp.pderiv i)

/-- Projection of the divergence numerator when the new denominator is
already homogeneous. -/
theorem component_polynomialDivNum {d : ℕ} {H : MvPolynomial σ R}
    (hd : 0 < d) (hH : H.IsHomogeneous d) (N : σ → MvPolynomial σ R) :
    homogeneousComponent (2*d) (polynomialDivNum H N) =
      polynomialDivNum H (fun i => homogeneousComponent (d+1) (N i)) := by
  have hderiv (i : σ) : (pderiv i H).IsHomogeneous (d-1) := by
    apply pderiv_isHomogeneous
    have he : d-1+1 = d := by omega
    simpa only [he] using hH
  simp only [polynomialDivNum, polynomialDivergence, polynomialDirectional, map_sub, map_sum]
  rw [show 2*d = d+d by omega, component_mul_homogeneous hH]
  simp only [map_sum, ← pderiv_component]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (N i), show d+d = (d-1)+(d+1) by omega,
    component_mul_homogeneous (hderiv i)]
  ring

theorem component_polynomialDirectional {f d : ℕ} {F : MvPolynomial σ R}
    (hF : F.IsHomogeneous (f+1)) (N : σ → MvPolynomial σ R) :
    homogeneousComponent (f+d) (polynomialDirectional F N) =
      polynomialDirectional F (fun i => homogeneousComponent d (N i)) := by
  simp only [polynomialDirectional, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (N i), component_mul_homogeneous (pderiv_isHomogeneous hF i)]
  ring

/-- A finite geometric sum; no rational function is integrated here. -/
def finiteInverse (D h : MvPolynomial σ R) (p : ℕ) : MvPolynomial σ R :=
  ∑ i ∈ Finset.range p, h^i * (h-D)^(p-1-i)

omit [Fintype σ] in
theorem finiteInverse_identity (D h : MvPolynomial σ R) (p : ℕ) :
    D*finiteInverse D h p = h^p - (h-D)^p := by
  rw [mul_comm]
  simpa only [finiteInverse, sub_sub_cancel] using geom_sum₂_mul h (h-D) p

/-- A normalized rational field with a legal initial denominator component
has homogeneous polynomial certificate data. The degree estimate is finite:
`p > d+1` suffices, and the new denominator has degree `p*d`.

The hypotheses allow a nonzero divergence quotient `Q`; this is the full
pole-order-one identity, not only its strict variant. -/
theorem homogeneous_data_from_initial_denominator
    [IsDomain R]
    (F A D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) (Q : MvPolynomial σ R)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (normal : polynomialDirectional F N = A*D)
    (divergence : polynomialDivNum D N = F*Q)
    (d : ℕ) (hd : 0 < d) (hD : HasOrder d D)
    (hlegal : ¬ F ∣ homogeneousComponent d D)
    (p : ℕ) (hp : d+1 < p) :
    ∃ H : MvPolynomial σ R, ∃ M : σ → MvPolynomial σ R, ∃ Q' : MvPolynomial σ R,
      H ≠ 0 ∧ H.IsHomogeneous (p*d) ∧ (∀ i, (M i).IsHomogeneous (p*d+1)) ∧
      IsRelPrime F H ∧ polynomialDirectional F M = A*H ∧
      polynomialDivNum H M = F*Q' := by
  classical
  let h := homogeneousComponent d D
  let H := h^p
  let U := (h-D)^p
  let S := finiteInverse D h p
  let M : σ → MvPolynomial σ R := fun i => S*N i
  let M' : σ → MvPolynomial σ R := fun i => homogeneousComponent (p*d+1) (M i)
  have hp0 : 0 < p := by omega
  have hpd : 0 < p*d := Nat.mul_pos hp0 hd
  have hh : h.IsHomogeneous d := homogeneousComponent_isHomogeneous d D
  have hH : H.IsHomogeneous (p*d) := by
    simpa only [H, Nat.mul_comm] using hh.pow p
  have hH0 : H ≠ 0 := by
    intro hz
    have hdiv : F ∣ h^p := by
      rw [show h^p = 0 from hz]
      exact dvd_zero F
    exact hlegal (hprime.dvd_of_dvd_pow hdiv)
  have hHlegal : IsRelPrime F H := by
    apply hprime.irreducible.isRelPrime_iff_not_dvd.mpr
    intro hv
    exact hlegal (hprime.dvd_of_dvd_pow hv)
  have hU : HasOrder (p*(d+1)) U := (order_sub_initial hD).pow p
  have hHorder : HasOrder (p*d) H := isHomogeneous_hasOrder hH
  have hDS : D*S = H-U := finiteInverse_identity D h p
  have hnormal : polynomialDirectional F M = A*(H-U) := by
    rw [show M = (fun i => S*N i) from rfl, polynomialDirectional_scale, normal]
    calc
      S*(A*D) = A*(D*S) := by ring
      _ = A*(H-U) := by rw [hDS]
  have hnormal' : polynomialDirectional F M' = A*H := by
    have hhcomp := congrArg (homogeneousComponent (p*d+6)) hnormal
    have hgrade : p*d+6 = 5+(p*d+1) := by omega
    rw [hgrade, component_polynomialDirectional (show F.IsHomogeneous (5+1) from hF)]
      at hhcomp
    have hAU : homogeneousComponent (p*d+6) (A*U) = 0 :=
      ((isHomogeneous_hasOrder hA).mul hU).component_eq_zero (by
        simp only [Nat.mul_add, Nat.mul_one]
        omega)
    have hAH : (A*H).IsHomogeneous (p*d+6) := by
      convert hA.mul hH using 1
      omega
    rw [← hgrade, mul_sub, map_sub, homogeneousComponent_eq_self hAH, hAU, sub_zero]
      at hhcomp
    exact hhcomp
  have herror : HasOrder (2*d+2*(p*d)+1)
      (-D*(H*polynomialDirectional U N-U*polynomialDirectional H N)) := by
    have hleft : HasOrder (p*d+p*(d+1)-1) (H*polynomialDirectional U N) :=
      (hHorder.mul (order_polynomialDirectional hU N)).mono (by omega)
    have hright : HasOrder (p*d+p*(d+1)-1) (U*polynomialDirectional H N) :=
      (hU.mul (order_polynomialDirectional hHorder N)).mono (by omega)
    have h := (hD.neg).mul (hleft.sub hright)
    exact h.mono (by
      simp only [Nat.mul_add, Nat.mul_one]
      omega)
  have hdivreplace := denominator_replacement_divergence D S H U N hDS
  rw [divergence] at hdivreplace
  have hproduct (k : ℕ) (hk : k ≤ 2*(p*d)) :
      F ∣ homogeneousComponent (2*d+k) (D^2*polynomialDivNum H M) := by
    rw [show M = (fun i => S*N i) from rfl, hdivreplace, sub_eq_add_neg, map_add]
    have hzero : homogeneousComponent (2*d+k)
        (-(D*(H*polynomialDirectional U N-U*polynomialDirectional H N))) = 0 := by
      apply HasOrder.component_eq_zero (by simpa only [neg_mul] using herror)
      omega
    rw [hzero, add_zero]
    exact component_dvd_of_dvd hF (dvd_mul_of_dvd_right (dvd_mul_right F Q) _) _
  have hCorder : HasOrder (2*d) (D^2) := by
    simpa only [pow_two, two_mul] using hD.mul hD
  have hClegal : ¬ F ∣ homogeneousComponent (2*d) (D^2) := by
    rw [pow_two, two_mul, component_mul_initial hD hD]
    intro hv
    exact (hprime.dvd_mul.mp hv).elim hlegal hlegal
  have hB := component_dvd_of_product hF hprime hCorder hClegal (2*(p*d)) hproduct
  rw [component_polynomialDivNum hpd hH] at hB
  obtain ⟨Q', hQ'⟩ := hB
  refine ⟨H, M', Q', hH0, hH, ?_, hHlegal, hnormal', hQ'⟩
  intro i
  exact homogeneousComponent_isHomogeneous (p*d+1) (M i)

end HoldoutConstruction

#print axioms HoldoutConstruction.denominator_replacement_divergence
#print axioms HoldoutConstruction.homogeneous_data_from_initial_denominator
end
end
