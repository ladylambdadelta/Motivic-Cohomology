import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Basic

noncomputable section

open scoped MonomialOrder

namespace Boundary
namespace PolynomialGroebnerBasics

variable {σ : Type*} [Fintype σ]
variable [DecidableEq σ]
variable {R : Type*} [CommSemiring R]

/-- The canonical lexicographic monomial order on `σ →₀ ℕ`. -/
abbrev lexMonomialOrder [LinearOrder σ] [WellFoundedGT σ] : MonomialOrder σ :=
  MonomialOrder.lex

/-- The leading monomial of a nonzero multivariate polynomial, defined constructively
by taking the maximum of its finite support in the chosen monomial order. -/
noncomputable def leadingMonomial (m : MonomialOrder σ) (p : MvPolynomial σ R) :
    σ →₀ ℕ :=
  by
    classical
    exact if h : p = 0 then 0 else
      m.toSyn.symm
        ((p.support.image m.toSyn).max'
          (by
            have hsup : p.support.Nonempty := by
              by_contra hs
              have hcoeff : ∀ d : σ →₀ ℕ, MvPolynomial.coeff d p = 0 := by
                intro d
                by_contra hnd
                exact hs ⟨d, by simpa [MvPolynomial.mem_support_iff, hnd]⟩
              exact h <| by
                ext d
                exact hcoeff d
            exact Finset.image_nonempty.2 hsup))

/-- The leading coefficient of a polynomial with respect to a fixed monomial order. -/
noncomputable def leadingCoeff (m : MonomialOrder σ) (p : MvPolynomial σ R) : R :=
  p.coeff (leadingMonomial m p)

/-- The leading term of a polynomial with respect to a fixed monomial order. -/
noncomputable def leadingTerm (m : MonomialOrder σ) (p : MvPolynomial σ R) :
    MvPolynomial σ R :=
  MvPolynomial.monomial (leadingMonomial m p) (leadingCoeff m p)

theorem leadingMonomial_eq_zero_of_eq_zero
    (m : MonomialOrder σ) (p : MvPolynomial σ R) (h : p = 0) :
    leadingMonomial m p = 0 := by
  simp [leadingMonomial, h]

theorem leadingMonomial_mem_support
    (m : MonomialOrder σ) {p : MvPolynomial σ R} (hp : p ≠ 0) :
    leadingMonomial m p ∈ p.support := by
  classical
  simp [leadingMonomial, hp]
  have hsup : p.support.Nonempty := by
    by_contra hs
    have hcoeff : ∀ d : σ →₀ ℕ, MvPolynomial.coeff d p = 0 := by
      intro d
      by_contra hnd
      exact hs ⟨d, by simpa [MvPolynomial.mem_support_iff, hnd]⟩
    exact hp <| by
      ext d
      exact hcoeff d
  let a : m.syn := (p.support.image m.toSyn).max' (Finset.image_nonempty.2 hsup)
  have ha : a ∈ p.support.image m.toSyn := by
    simpa [a] using Finset.max'_mem (p.support.image m.toSyn) (Finset.image_nonempty.2 hsup)
  rcases Finset.mem_image.mp ha with ⟨q, hq, hqeq⟩
  have hqe' : m.toSyn q = m.toSyn (m.toSyn.symm a) := by
    simpa [hqeq]
  have hqe : q = m.toSyn.symm a := by
    exact m.toSyn.injective hqe'
  simpa [leadingMonomial, a, hqe] using hq

theorem leadingCoeff_ne_zero
    (m : MonomialOrder σ) {p : MvPolynomial σ R} (hp : p ≠ 0) :
    leadingCoeff m p ≠ 0 := by
  classical
  rw [leadingCoeff]
  intro hzero
  have hmem := leadingMonomial_mem_support (m := m) (p := p) hp
  rw [MvPolynomial.mem_support_iff] at hmem
  exact hmem hzero

theorem leadingTerm_apply
    (m : MonomialOrder σ) {p : MvPolynomial σ R} (hp : p ≠ 0) :
    leadingTerm m p = MvPolynomial.monomial (leadingMonomial m p) (p.coeff (leadingMonomial m p)) := by
  rfl

theorem leadingTerm_coeff
    (m : MonomialOrder σ) {p : MvPolynomial σ R} (hp : p ≠ 0) :
    (leadingTerm m p).coeff (leadingMonomial m p) = leadingCoeff m p := by
  simp [leadingTerm, leadingCoeff]

end PolynomialGroebnerBasics
end Boundary
