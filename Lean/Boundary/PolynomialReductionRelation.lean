import Boundary.PolynomialReduction
import Boundary.PolynomialNormalForm

noncomputable section

open scoped MonomialOrder

namespace Boundary
namespace PolynomialReductionRelation

variable {σ : Type*} [Fintype σ]
variable [DecidableEq σ]
variable {k : Type*} [Field k]
variable (m : MonomialOrder σ)

/-- A polynomial is reducible by a finite list if one element of the list has a dividing
leading monomial. -/
def reducibleByList (G : List (MvPolynomial σ k)) (f : MvPolynomial σ k) : Prop :=
  ∃ g ∈ G, Boundary.PolynomialReduction.reducibleByLeadingTerm (m := m) g f

/-- Choose a reducer from a nonempty reducibility witness. -/
noncomputable def findReducer
    (G : List (MvPolynomial σ k))
    (f : MvPolynomial σ k) :
    Option { g // g ∈ G ∧ Boundary.PolynomialReduction.reducibleByLeadingTerm (m := m) g f } :=
  match G with
  | [] => none
  | g :: G =>
      by
        classical
        if hg : Boundary.PolynomialReduction.reducibleByLeadingTerm (m := m) g f then
          exact some ⟨g, by simp, hg⟩
        else
          match findReducer G f with
          | none => exact none
          | some g' =>
              exact some
                ⟨g'.1, by
                  have hmem : g'.1 = g ∨ g'.1 ∈ G := Or.inr g'.2.1
                  have hmem' : g'.1 ∈ g :: G := by
                    simpa [List.mem_cons] using hmem
                  exact ⟨hmem', g'.2.2⟩⟩

theorem findReducer_isSome_of_reducible
    (G : List (MvPolynomial σ k))
    (f : MvPolynomial σ k)
    (h : reducibleByList (m := m) G f) :
    (findReducer (m := m) G f).isSome := by
  classical
  induction G with
  | nil =>
      rcases h with ⟨g, hg, hred⟩
      cases hg
  | cons g G ih =>
      by_cases hg : Boundary.PolynomialReduction.reducibleByLeadingTerm (m := m) g f
      · simp [findReducer, hg]
      · rcases h with ⟨g', hg', hred⟩
        simp at hg'
        rcases hg' with rfl | hg'
        · exact False.elim (hg hred)
        · have htail : reducibleByList (m := m) G f := by
            exact ⟨g', hg', hred⟩
          have hrec := ih htail
          cases hfind : findReducer (m := m) G f with
          | none =>
              simp [findReducer, hg, hfind] at hrec
          | some g' =>
              simp [findReducer, hg, hfind]

/-- Choose a reducer from a nonempty reducibility witness. -/
noncomputable def chooseReducer
    (G : List (MvPolynomial σ k))
    (f : MvPolynomial σ k)
    (h : reducibleByList (m := m) G f) :
    { g // g ∈ G ∧ Boundary.PolynomialReduction.reducibleByLeadingTerm (m := m) g f } := by
  classical
  exact (findReducer (m := m) G f).get (findReducer_isSome_of_reducible (m := m) G f h)

theorem chooseReducer_spec
    (G : List (MvPolynomial σ k))
    (f : MvPolynomial σ k)
    (h : reducibleByList (m := m) G f) :
    (chooseReducer (m := m) G f h).1 ∈ G ∧
      Boundary.PolynomialReduction.reducibleByLeadingTerm (m := m)
        (chooseReducer (m := m) G f h).1 f := by
  classical
  have hsome := findReducer_isSome_of_reducible (m := m) G f h
  cases hfind : findReducer (m := m) G f with
  | none =>
      simp [hfind] at hsome
  | some g =>
      simpa [chooseReducer, hfind] using g.2

/-- A finite-list reduction step uses a chosen reducer from the list. -/
noncomputable def listReductionStep
    (G : List (MvPolynomial σ k))
    (f : MvPolynomial σ k)
    (h : reducibleByList (m := m) G f) :
    MvPolynomial σ k :=
  Boundary.PolynomialReduction.reductionStep (m := m)
    (chooseReducer (m := m) G f h) f
    (by
      rcases chooseReducer_spec (m := m) G f h with ⟨hg, hgred⟩
      exact hgred)

theorem leadingMonomial_listReductionStep_lt
    (G : List (MvPolynomial σ k))
    (f : MvPolynomial σ k)
    (hf : f ≠ 0)
    (h : reducibleByList (m := m) G f)
    (hnonzero : listReductionStep (m := m) G f h ≠ 0) :
    PolynomialGroebnerBasics.leadingMonomial m
        (listReductionStep (m := m) G f h) ≺[m]
      PolynomialGroebnerBasics.leadingMonomial m f := by
  unfold listReductionStep
  rcases chooseReducer_spec (m := m) G f h with ⟨hg, hgred⟩
  exact Boundary.PolynomialReduction.leadingMonomial_reductionStep_lt
    (m := m)
    (g := (chooseReducer (m := m) G f h).1)
    (f := f)
    hf
    hgred
    hnonzero

/-- The reducer selected from a reducible finite list. -/
abbrev selectedReducer
    (G : List (MvPolynomial σ k))
    (f : MvPolynomial σ k)
    (h : reducibleByList (m := m) G f) :
    { g // g ∈ G ∧ Boundary.PolynomialReduction.reducibleByLeadingTerm (m := m) g f } :=
  chooseReducer (m := m) G f h

theorem listReductionStep_add
    (G : List (MvPolynomial σ k))
    (f : MvPolynomial σ k)
    (h : reducibleByList (m := m) G f) :
    listReductionStep (m := m) G f h +
      (MvPolynomial.monomial
        (Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m (selectedReducer (m := m) G f h).1)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (by
            rcases chooseReducer_spec (m := m) G f h with ⟨hg, hgred⟩
            exact hgred.2.2))
        (PolynomialGroebnerBasics.leadingCoeff m f /
          PolynomialGroebnerBasics.leadingCoeff m (selectedReducer (m := m) G f h).1) *
        (selectedReducer (m := m) G f h).1) = f := by
  unfold listReductionStep selectedReducer
  rcases chooseReducer_spec (m := m) G f h with ⟨hg, hgred⟩
  rw [Boundary.PolynomialReduction.reductionStep]
  exact sub_add_cancel _ _

/-- A finite-list reduction step differs from the original polynomial by an element of the
finite list span. -/
theorem listReductionStep_sub_mem_listSpan
    (G : List (MvPolynomial σ k))
    (f : MvPolynomial σ k)
    (h : reducibleByList (m := m) G f) :
    f - listReductionStep (m := m) G f h ∈
      Boundary.PolynomialNormalForm.listSpan (σ := σ) (k := k) G := by
  have hadd := listReductionStep_add (m := m) G f h
  have hsel :
      (selectedReducer (m := m) G f h).1 ∈ G :=
    (chooseReducer_spec (m := m) G f h).1
  have hmem :
      MvPolynomial.monomial
        (Boundary.PolynomialReduction.monomialQuotient
          (PolynomialGroebnerBasics.leadingMonomial m (selectedReducer (m := m) G f h).1)
          (PolynomialGroebnerBasics.leadingMonomial m f)
          (by
            rcases chooseReducer_spec (m := m) G f h with ⟨hg, hgred⟩
            exact hgred.2.2))
        (PolynomialGroebnerBasics.leadingCoeff m f /
          PolynomialGroebnerBasics.leadingCoeff m (selectedReducer (m := m) G f h).1) *
        (selectedReducer (m := m) G f h).1 ∈
      Boundary.PolynomialNormalForm.listSpan (σ := σ) (k := k) G := by
    exact Ideal.mul_mem_left _ _
      (Boundary.PolynomialNormalForm.mem_listSpan_of_mem_list
        (σ := σ) (k := k) (G := G) hsel)
  have hstep :
      f - listReductionStep (m := m) G f h =
        MvPolynomial.monomial
          (Boundary.PolynomialReduction.monomialQuotient
            (PolynomialGroebnerBasics.leadingMonomial m (selectedReducer (m := m) G f h).1)
            (PolynomialGroebnerBasics.leadingMonomial m f)
            (by
              rcases chooseReducer_spec (m := m) G f h with ⟨hg, hgred⟩
              exact hgred.2.2))
          (PolynomialGroebnerBasics.leadingCoeff m f /
            PolynomialGroebnerBasics.leadingCoeff m (selectedReducer (m := m) G f h).1) *
          (selectedReducer (m := m) G f h).1 := by
    have hf : f =
        listReductionStep (m := m) G f h +
          (MvPolynomial.monomial
            (Boundary.PolynomialReduction.monomialQuotient
              (PolynomialGroebnerBasics.leadingMonomial m (selectedReducer (m := m) G f h).1)
              (PolynomialGroebnerBasics.leadingMonomial m f)
              (by
                rcases chooseReducer_spec (m := m) G f h with ⟨hg, hgred⟩
                exact hgred.2.2))
            (PolynomialGroebnerBasics.leadingCoeff m f /
              PolynomialGroebnerBasics.leadingCoeff m (selectedReducer (m := m) G f h).1) *
            (selectedReducer (m := m) G f h).1) := by
      simpa [add_comm, add_left_comm, add_assoc] using hadd.symm
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      congrArg (fun x => x - listReductionStep (m := m) G f h) hf
  rw [hstep]
  exact hmem

end PolynomialReductionRelation
end Boundary
