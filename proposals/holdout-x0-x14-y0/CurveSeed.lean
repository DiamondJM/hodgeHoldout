import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

/- Source component: CurveSeed -/
section
/-!
An exact characteristic-zero seed for the weighted-conic construction.

This is an intermediate construction lemma, not a HasCertificate theorem.
The parameter lies in (7,8), where all denominators and both explicit
evaluation minors are nonzero. Existence uses the intermediate value
theorem; no modular-to-characteristic-zero lifting is assumed.
-/

noncomputable section

namespace HoldoutConic

def f (r : ℝ) : ℝ :=
  r^23 - 14*r^22 + 86*r^21 - 290*r^20 + 520*r^19 - 199*r^18 -
  94566*r^17 + 1029405*r^16 - 5018220*r^15 + 13903481*r^14 -
  22713424*r^13 + 17780092*r^12 + 9399696*r^11 - 47299809*r^10 +
  72791853*r^9 - 73173409*r^8 + 54302525*r^7 - 30776930*r^6 +
  13325391*r^5 - 4325886*r^4 + 1016955*r^3 - 163296*r^2 + 16038*r - 729

def m (r : ℝ) : ℝ := r^4 - 4*r^3 + 5*r^2 + r - 2

def gEven (r : ℝ) : ℝ :=
  16*r^11 - 80*r^10 + 96*r^9 + 144*r^8 - 380*r^7 + 240*r^6 +
  84*r^5 - 178*r^4 + 63*r^3 + 9*r^2 - 8*r + 1

def gOdd (r : ℝ) : ℝ :=
  8*r^11 - 48*r^10 + 112*r^9 - 16*r^8 - 224*r^7 + 352*r^6 -
  275*r^5 + 101*r^4 + 11*r^3 - 24*r^2 + 8*r - 1

theorem m_pos {r : ℝ} (hr : 7 < r) : 0 < m r := by
  have hu : 0 < r - 7 := by linarith
  have he : m r = (r-7)^4 + 24*(r-7)^3 + 215*(r-7)^2 +
      855*(r-7) + 1279 := by unfold m; ring
  rw [he]
  positivity

theorem gEven_pos {r : ℝ} (hr : 7 < r) : 0 < gEven r := by
  have hu : 0 < r - 7 := by linarith
  have he : gEven r =
      16*(r-7)^11 + 1152*(r-7)^10 + 37616*(r-7)^9 +
      735312*(r-7)^8 + 9561508*(r-7)^7 + 86845684*(r-7)^6 +
      562259880*(r-7)^5 + 2594920654*(r-7)^4 +
      8367064363*(r-7)^3 + 17953176796*(r-7)^2 +
      23074297147*(r-7) + 13459581409 := by unfold gEven; ring
  rw [he]
  positivity

theorem gOdd_pos {r : ℝ} (hr : 7 < r) : 0 < gOdd r := by
  have hu : 0 < r - 7 := by linarith
  have he : gOdd r =
      8*(r-7)^11 + 568*(r-7)^10 + 18312*(r-7)^9 +
      353960*(r-7)^8 + 4559408*(r-7)^7 + 41110960*(r-7)^6 +
      264892829*(r-7)^5 + 1220302940*(r-7)^4 +
      3941171329*(r-7)^3 + 8504139347*(r-7)^2 +
      11041457694*(r-7) + 6539731204 := by unfold gOdd; ring
  rw [he]
  positivity

theorem exists_parameter : ∃ r : ℝ, 7 < r ∧ r < 8 ∧ f r = 0 := by
  have h7 : f 7 = -1000427543178133743 := by norm_num [f]
  have h8 : f 8 = 37662822436086419543 := by norm_num [f]
  have hc : Continuous f := by unfold f; fun_prop
  have hz : (0 : ℝ) ∈ Set.Icc (f 7) (f 8) := by
    rw [h7, h8]
    constructor <;> norm_num
  obtain ⟨r, hr, hf⟩ := intermediate_value_Icc (by norm_num : (7 : ℝ) ≤ 8)
    hc.continuousOn hz
  refine ⟨r, ?_, ?_, hf⟩
  · rcases lt_or_eq_of_le hr.1 with h | h
    · exact h
    · subst r; linarith
  · rcases lt_or_eq_of_le hr.2 with h | h
    · exact h
    · subst r; linarith

def R (r : ℝ) : ℝ := r*(1-r-r^2)/(1-r)
def M (r : ℝ) : ℝ := r^2*m r/(r-1)^2
def a (r : ℝ) : ℝ := 3*(1-2*r)/(1-r)
def b (r : ℝ) : ℝ := 3*(1-2*r)

theorem R_pos {r : ℝ} (hr : 7 < r) : 0 < R r := by
  have hr0 : 0 < r := by linarith
  have hnum : 1-r-r^2 < 0 := by nlinarith [sq_nonneg r]
  have hden : 1-r < 0 := by linarith
  exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hr0 hnum) hden

theorem M_pos {r : ℝ} (hr : 7 < r) : 0 < M r := by
  have hr0 : 0 < r := by linarith
  have hd : 0 < r - 1 := by linarith
  unfold M
  exact div_pos (mul_pos (sq_pos_of_pos hr0) (m_pos hr)) (sq_pos_of_pos hd)

theorem a_ne_zero {r : ℝ} (hr : 7 < r) : a r ≠ 0 := by
  unfold a
  apply div_ne_zero
  · apply mul_ne_zero (by norm_num)
    linarith
  · linarith

theorem b_ne_zero {r : ℝ} (hr : 7 < r) : b r ≠ 0 := by
  unfold b
  apply mul_ne_zero (by norm_num)
  linarith

theorem parameter_relation {r : ℝ} (hr : 7 < r) (hf : f r = 0) :
    (a r)^6 / (M r * R r) + (b r)^6 / (M r)^3 = 1 := by
  have hr0 : r ≠ 0 := by linarith
  have hr1 : r - 1 ≠ 0 := by linarith
  have hr1' : 1 - r ≠ 0 := by linarith
  have hm : m r ≠ 0 := ne_of_gt (m_pos hr)
  have hquad : 1-r-r^2 ≠ 0 := by nlinarith [sq_nonneg r]
  unfold a b M R
  field_simp
  unfold f at hf
  unfold m
  nlinarith only [hf]

theorem coefficient_relations {r : ℝ} (hr : 7 < r) :
    a r*r + 3*r^2 - 3*R r = 0 ∧
    a r + 3*r^2 + 6*r - 3*R r - 3 = 0 ∧
    M r + b r*r + 3*r^2 + 6*r*R r - (R r)^2 - 3*R r = 0 ∧
    b r + 6*r - 3 = 0 := by
  have h1 : 1-r ≠ 0 := by linarith
  have h2 : r-1 ≠ 0 := by linarith
  unfold a b M R m
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  · ring

structure Seed where
  r : ℝ
  lower : 7 < r
  upper : r < 8
  root : f r = 0
  q : ℂ
  k : ℂ
  q_power : q^4 = (R r : ℂ)
  k_power : k^6 = (M r : ℂ)/q^2

theorem Seed.q_ne_zero (p : Seed) : p.q ≠ 0 := by
  intro h
  have hq := p.q_power
  rw [h, zero_pow (by decide)] at hq
  have hR : R p.r ≠ 0 := ne_of_gt (R_pos p.lower)
  exact hR (by exact_mod_cast hq.symm)

theorem Seed.k_ne_zero (p : Seed) : p.k ≠ 0 := by
  have hM : (M p.r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (M_pos p.lower)
  intro h
  have hk := p.k_power
  rw [h, zero_pow (by decide)] at hk
  exact (div_ne_zero hM (pow_ne_zero 2 p.q_ne_zero)) hk.symm

theorem exists_seed : Nonempty Seed := by
  obtain ⟨r, hl, hu, hf⟩ := exists_parameter
  obtain ⟨q, hq⟩ := IsAlgClosed.exists_pow_nat_eq (R r : ℂ) (by decide : 0 < 4)
  obtain ⟨k, hk⟩ := IsAlgClosed.exists_pow_nat_eq ((M r : ℂ)/q^2) (by decide : 0 < 6)
  exact ⟨⟨r, hl, hu, hf, q, k, hq, hk⟩⟩

def Seed.alpha (p : Seed) : ℂ := (a p.r : ℂ)/(p.k*p.q)
def Seed.beta (p : Seed) : ℂ := (b p.r : ℂ)/(p.k^3*p.q)

theorem Seed.base_relation (p : Seed) : p.alpha^6 + p.beta^6 = 1 := by
  have hR : (R p.r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (R_pos p.lower)
  have hM : (M p.r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (M_pos p.lower)
  have hp : (a p.r : ℂ)^6 / ((M p.r : ℂ)*(R p.r : ℂ)) +
      (b p.r : ℂ)^6 / (M p.r : ℂ)^3 = 1 := by
    exact_mod_cast parameter_relation p.lower p.root
  have hkq : p.k^6*p.q^2 = (M p.r : ℂ) := by
    rw [p.k_power]
    field_simp [p.q_ne_zero]
  have hden1 : (p.k*p.q)^6 = (M p.r : ℂ)*(R p.r : ℂ) := by
    calc
      _ = (p.k^6*p.q^2)*p.q^4 := by ring
      _ = _ := by rw [hkq, p.q_power]
  have hden2 : (p.k^3*p.q)^6 = (M p.r : ℂ)^3 := by
    calc
      _ = (p.k^6*p.q^2)^3 := by ring
      _ = _ := by rw [hkq]
  simpa only [Seed.alpha, Seed.beta, div_pow, hden1, hden2] using hp

def H (alpha beta x0 x1 x2 S P : ℂ) : ℂ :=
  x0^6 + x1^6 + x2^6 + P*(alpha*x0^3*x1 + beta*x1^3*x2) + S^3 - 3*S*P^2

def scaledH (_r z x0 x1 x2 S Q : ℂ) (mm aa bb : ℂ) : ℂ :=
  z*(x0^6+x2^6+S^3) + mm*x1^6 + aa*x0^3*x1*Q + bb*x1^3*x2*Q - 3*S*Q^2

theorem scaled_curve_identity (r z mm aa bb : ℂ)
    (h2 : aa*r + 3*r^2 - 3*z^2 = 0)
    (h4 : aa + 3*r^2 + 6*r - 3*z^2 - 3 = 0)
    (h6 : mm + bb*r + 3*r^2 + 6*r*z^2 - z^4 - 3*z^2 = 0)
    (h8 : bb + 6*r - 3 = 0) (s t : ℂ) :
    scaledH r z (s^2) (s*t) (t^2)
      (-(s^4+z*s^2*t^2+t^4)) (r*s^3*t+z*s*t^3) mm aa bb = 0 := by
  unfold scaledH
  linear_combination s^10*t^2*h2 + z*s^8*t^4*h4 + s^6*t^6*h6 + z*s^4*t^8*h8

theorem Seed.scaled_curve (p : Seed) (s t : ℂ) :
    scaledH (p.r : ℂ) (p.q^2) (s^2) (s*t) (t^2)
      (-(s^4+p.q^2*s^2*t^2+t^4)) ((p.r : ℂ)*s^3*t+p.q^2*s*t^3)
      (M p.r : ℂ) (a p.r : ℂ) (b p.r : ℂ) = 0 := by
  obtain ⟨h2, h4, h6, h8⟩ := coefficient_relations p.lower
  have hqq : (p.q^2)^2 = (R p.r : ℂ) := by
    rw [← pow_mul, show 2*2=4 by decide, p.q_power]
  apply scaled_curve_identity
  · rw [hqq]; exact_mod_cast h2
  · rw [hqq]; exact_mod_cast h4
  · rw [show (p.q^2)^4 = ((p.q^2)^2)^2 by ring, hqq]
    exact_mod_cast h6
  · exact_mod_cast h8

theorem Seed.curve (p : Seed) (s t : ℂ) :
    H p.alpha p.beta (s^2) (p.k*s*t) (t^2)
      (-(s^4+p.q^2*s^2*t^2+t^4))
      (((p.r : ℂ)/p.q)*s^3*t+p.q*s*t^3) = 0 := by
  have hq := p.q_ne_zero
  have hk := p.k_ne_zero
  have hc := p.scaled_curve s t
  have hm : p.k^6*p.q^2 = (M p.r : ℂ) := by
    rw [p.k_power]
    field_simp
  have he : p.q^2 * H p.alpha p.beta (s^2) (p.k*s*t) (t^2)
      (-(s^4+p.q^2*s^2*t^2+t^4))
      (((p.r : ℂ)/p.q)*s^3*t+p.q*s*t^3) =
    scaledH (p.r : ℂ) (p.q^2) (s^2) (s*t) (t^2)
      (-(s^4+p.q^2*s^2*t^2+t^4)) ((p.r : ℂ)*s^3*t+p.q^2*s*t^3)
      (M p.r : ℂ) (a p.r : ℂ) (b p.r : ℂ) := by
    unfold H scaledH Seed.alpha Seed.beta
    field_simp
    linear_combination s^6*t^6*hm
  rw [hc] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hq)

end HoldoutConic

#print axioms HoldoutConic.exists_parameter
#print axioms HoldoutConic.parameter_relation
#print axioms HoldoutConic.exists_seed
#print axioms HoldoutConic.Seed.base_relation
#print axioms HoldoutConic.Seed.curve
end
end
