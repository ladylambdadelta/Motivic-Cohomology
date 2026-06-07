import Mathlib.Tactic
import Boundary.PolynomialGroebnerBasics

noncomputable section

open scoped MonomialOrder

namespace Boundary
namespace PolynomialReduction

variable {σ : Type*} [Fintype σ]
variable [DecidableEq σ]
variable {k : Type*} [Field k]

/-- Monomial divisibility in the exponent monoid. -/
def monomialDivides (a b : σ →₀ ℕ) : Prop :=
  a ≤ b

/-- The quotient monomial exponent for a divisibility witness. -/
def monomialQuotient (a b : σ →₀ ℕ) (h : monomialDivides a b) : σ →₀ ℕ :=
  b - a

theorem monomialQuotient_add (a b : σ →₀ ℕ) (h : monomialDivides a b) :
    monomialQuotient a b h + a = b := by
  ext i
  change (b i - a i) + a i = b i
  simpa [add_comm] using add_tsub_cancel_of_le (h i)

theorem monomialQuotient_sub (a b : σ →₀ ℕ) (h : monomialDivides a b) :
    b - monomialQuotient a b h = a := by
  ext i
  change b i - (b i - a i) = a i
  have h1 : b i = a i + (b i - a i) := by
    exact (add_tsub_cancel_of_le (h i)).symm
  exact (Nat.sub_eq_iff_eq_add (Nat.sub_le _ _)).2 h1

/-- A polynomial is reducible by the leading term of `g` if the leading monomial of `g`
divides the leading monomial of the target polynomial, and the target is nonzero. -/
def reducibleByLeadingTerm (m : MonomialOrder σ) (g f : MvPolynomial σ k) : Prop :=
  f ≠ 0 ∧ g ≠ 0 ∧ monomialDivides (PolynomialGroebnerBasics.leadingMonomial m g)
    (PolynomialGroebnerBasics.leadingMonomial m f)

/-- One reduction step of `f` by `g`, using the leading term of `g`. -/
def reductionStep (m : MonomialOrder σ) (g f : MvPolynomial σ k)
    (h : reducibleByLeadingTerm m g f) : MvPolynomial σ k :=
  f -
    (MvPolynomial.monomial
        (monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
          (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2)
        (PolynomialGroebnerBasics.leadingCoeff m f /
          PolynomialGroebnerBasics.leadingCoeff m g) * g)

theorem support_leadingMonomial
    (m : MonomialOrder σ) {p : MvPolynomial σ k} (hp : p ≠ 0)
    {d : σ →₀ ℕ} (hd : d ∈ p.support) :
    d ≼[m] PolynomialGroebnerBasics.leadingMonomial m p := by
  classical
  let a : m.syn :=
    (p.support.image m.toSyn).max'
      (by
        have hsup : p.support.Nonempty := by
          by_contra hs
          have hcoeff : ∀ e : σ →₀ ℕ, MvPolynomial.coeff e p = 0 := by
            intro e
            by_contra hne
            exact hs ⟨e, by simpa [MvPolynomial.mem_support_iff, hne]⟩
          exact hp <| by
            ext e
            exact hcoeff e
        exact Finset.image_nonempty.2 hsup)
  have hmem : m.toSyn d ∈ p.support.image m.toSyn := by
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hle : m.toSyn d ≤ a := Finset.le_max' _ _ hmem
  have hdef :
      PolynomialGroebnerBasics.leadingMonomial m p = m.toSyn.symm a := by
    simp [PolynomialGroebnerBasics.leadingMonomial, hp, a]
  rw [hdef]
  rw [m.toSyn.apply_symm_apply]
  exact hle

theorem coeff_reductionStep_eq_zero_of_leadingMonomial_le
    (m : MonomialOrder σ) {g f : MvPolynomial σ k}
    (hf : f ≠ 0) (h : reducibleByLeadingTerm m g f)
    {d : σ →₀ ℕ} (hd : PolynomialGroebnerBasics.leadingMonomial m f ≼[m] d) :
    MvPolynomial.coeff d (reductionStep m g f h) = 0 := by
  classical
  unfold reductionStep
  rw [MvPolynomial.coeff_sub]
  by_cases hEq : d = PolynomialGroebnerBasics.leadingMonomial m f
  · subst hEq
    have hgt : PolynomialGroebnerBasics.leadingCoeff m g ≠ 0 :=
      PolynomialGroebnerBasics.leadingCoeff_ne_zero (m := m) h.2.1
    have hsle :
        monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
            (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2
          ≤ PolynomialGroebnerBasics.leadingMonomial m f := by
      intro i
      simp [monomialQuotient]
    have hsub :
        PolynomialGroebnerBasics.leadingMonomial m f -
            monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
              (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2
          = PolynomialGroebnerBasics.leadingMonomial m g := by
      simpa [monomialQuotient] using
        (monomialQuotient_sub
          (a := PolynomialGroebnerBasics.leadingMonomial m g)
          (b := PolynomialGroebnerBasics.leadingMonomial m f)
          h.2.2)
    have hcoeffprod :
        MvPolynomial.coeff (PolynomialGroebnerBasics.leadingMonomial m f)
            (MvPolynomial.monomial
                (monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
                  (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2)
                (PolynomialGroebnerBasics.leadingCoeff m f /
                  PolynomialGroebnerBasics.leadingCoeff m g) * g)
          = PolynomialGroebnerBasics.leadingCoeff m f := by
      rw [MvPolynomial.coeff_monomial_mul', if_pos hsle, hsub]
      change
        (PolynomialGroebnerBasics.leadingCoeff m f /
            PolynomialGroebnerBasics.leadingCoeff m g) *
          PolynomialGroebnerBasics.leadingCoeff m g =
          PolynomialGroebnerBasics.leadingCoeff m f
      exact
        (div_mul_cancel₀ (PolynomialGroebnerBasics.leadingCoeff m f) hgt)
    rw [hcoeffprod]
    simp [PolynomialGroebnerBasics.leadingCoeff]
  · have hgt : PolynomialGroebnerBasics.leadingMonomial m f ≺[m] d := by
      exact lt_of_le_of_ne hd (by simpa [eq_comm] using hEq)
    have hfzero : MvPolynomial.coeff d f = 0 := by
      by_contra hne
      have hdmem : d ∈ f.support := by
        simpa [MvPolynomial.mem_support_iff] using hne
      have hle := support_leadingMonomial (m := m) (p := f) hf hdmem
      exact (lt_irrefl _ <| lt_of_lt_of_le hgt hle)
    have hnotin : d ∉ (MvPolynomial.monomial
        (monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
          (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2)
        (PolynomialGroebnerBasics.leadingCoeff m f /
          PolynomialGroebnerBasics.leadingCoeff m g) * g).support := by
      intro hdmem
      have hsup := MvPolynomial.support_mul
        (MvPolynomial.monomial
          (monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
            (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2)
          (PolynomialGroebnerBasics.leadingCoeff m f /
            PolynomialGroebnerBasics.leadingCoeff m g)) g hdmem
      have hr :
          PolynomialGroebnerBasics.leadingCoeff m f / PolynomialGroebnerBasics.leadingCoeff m g ≠ 0 := by
        exact div_ne_zero (PolynomialGroebnerBasics.leadingCoeff_ne_zero (m := m) hf) (by
          exact PolynomialGroebnerBasics.leadingCoeff_ne_zero (m := m) h.2.1)
      rw [MvPolynomial.support_monomial, if_neg hr] at hsup
      rcases Finset.mem_add.mp hsup with ⟨a, ha, b, hb, hab⟩
      have ha' : a = monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
          (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2 := by
        exact Finset.mem_singleton.mp ha
      subst a
      have hble :
          b ≼[m] PolynomialGroebnerBasics.leadingMonomial m g :=
        support_leadingMonomial (m := m) (p := g) h.2.1 hb
      have hsum :
          monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
              (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2 + b
            ≼[m] PolynomialGroebnerBasics.leadingMonomial m f := by
        have hle' :
            monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
                (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2 + b
              ≼[m]
              monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
                (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2 +
                PolynomialGroebnerBasics.leadingMonomial m g := by
          change
            m.toSyn
                (monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
                  (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2 + b) ≤
              m.toSyn
                (monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
                  (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2 +
                PolynomialGroebnerBasics.leadingMonomial m g)
          simpa [map_add] using
            add_le_add_left (show
              m.toSyn b ≤ m.toSyn (PolynomialGroebnerBasics.leadingMonomial m g) from hble)
              (m.toSyn
                (monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
                  (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2))
        simpa [monomialQuotient_add] using hle'
      have hle' : d ≼[m] PolynomialGroebnerBasics.leadingMonomial m f := by
        simpa [hab] using hsum
      exact (lt_irrefl _ <| lt_of_lt_of_le hgt hle')
    have hprodzero :
        MvPolynomial.coeff d
            (MvPolynomial.monomial
                (monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
                  (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2)
                (PolynomialGroebnerBasics.leadingCoeff m f /
                  PolynomialGroebnerBasics.leadingCoeff m g) * g)
          = 0 := by
      exact MvPolynomial.not_mem_support_iff.mp hnotin
    simp [reductionStep, hfzero, hprodzero]

theorem support_reductionStep_subset_lower
    (m : MonomialOrder σ) {g f : MvPolynomial σ k}
    (hf : f ≠ 0) (h : reducibleByLeadingTerm m g f) :
    ∀ {d : σ →₀ ℕ}, d ∈ (reductionStep m g f h).support →
      d ≺[m] PolynomialGroebnerBasics.leadingMonomial m f := by
  intro d hd
  by_contra hnot
  have hle : PolynomialGroebnerBasics.leadingMonomial m f ≼[m] d := by
    exact not_lt.mp hnot
  have hzero := coeff_reductionStep_eq_zero_of_leadingMonomial_le (m := m) (g := g) (f := f) hf h
    (d := d) hle
  exact (MvPolynomial.mem_support_iff.mp hd) hzero

theorem leadingMonomial_reductionStep_lt
    (m : MonomialOrder σ) {g f : MvPolynomial σ k}
    (hf : f ≠ 0) (h : reducibleByLeadingTerm m g f)
    (hnonzero : reductionStep m g f h ≠ 0) :
    PolynomialGroebnerBasics.leadingMonomial m (reductionStep m g f h) ≺[m]
      PolynomialGroebnerBasics.leadingMonomial m f := by
  have hmem :=
    PolynomialGroebnerBasics.leadingMonomial_mem_support (m := m)
      (p := reductionStep m g f h) hnonzero
  exact support_reductionStep_subset_lower (m := m) (g := g) (f := f) hf h hmem

theorem reductionStep_add
    (m : MonomialOrder σ) {g f : MvPolynomial σ k}
    (h : reducibleByLeadingTerm m g f) :
    reductionStep m g f h +
      (MvPolynomial.monomial
        (monomialQuotient (PolynomialGroebnerBasics.leadingMonomial m g)
          (PolynomialGroebnerBasics.leadingMonomial m f) h.2.2)
        (PolynomialGroebnerBasics.leadingCoeff m f /
          PolynomialGroebnerBasics.leadingCoeff m g) * g) = f := by
  rw [reductionStep]
  exact sub_add_cancel _ _

end PolynomialReduction
end Boundary
