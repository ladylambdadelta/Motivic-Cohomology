import Boundary.PolynomialSmoothness.StandardSmoothDimensionZero
import Boundary.PolynomialSmoothness.StandardSmoothTransport
import Boundary.PolynomialSmoothness.JacobianTransport
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Determinant

namespace Boundary

noncomputable section

namespace _root_.Algebra

open scoped Polynomial

theorem mvPolynomial_fin_one_isStandardSmoothOfRelativeDimension
    (A : Type*) [CommRing A] :
    Algebra.IsStandardSmoothOfRelativeDimension.{0, 0} 1 A (MvPolynomial (Fin 1) A) := by
  let G : Algebra.Generators A (MvPolynomial (Fin 1) A) := {
    vars := Fin 1,
    val := MvPolynomial.X,
    σ' := fun p => p,
    aeval_val_σ' := by
      intro p
      change MvPolynomial.aeval MvPolynomial.X p = p
      exact MvPolynomial.aeval_X_left_apply p
  }
  let P : Algebra.Presentation A (MvPolynomial (Fin 1) A) := {
    toGenerators := G,
    rels := PEmpty,
    relation := PEmpty.elim,
    span_range_relation_eq_ker := by
      have hSpan :
          Ideal.span (Set.range (PEmpty.elim : PEmpty → MvPolynomial (Fin 1) A)) =
            (⊥ : Ideal (MvPolynomial (Fin 1) A)) := by
        have hZero :
            (Set.range (PEmpty.elim : PEmpty → MvPolynomial (Fin 1) A)) =
              (∅ : Set (MvPolynomial (Fin 1) A)) := by
          ext x
          constructor
          · rintro ⟨a, rfl⟩
            cases a
          · intro hx
            exact False.elim hx
        rw [hZero]
        exact Ideal.span_empty
      have hAevalKer :
          RingHom.ker (MvPolynomial.aeval G.val) =
            (⊥ : Ideal (MvPolynomial (Fin 1) A)) := by
        change RingHom.ker (MvPolynomial.aeval MvPolynomial.X) =
          (⊥ : Ideal (MvPolynomial (Fin 1) A))
        rw [MvPolynomial.aeval_X_left]
        ext x
        rw [RingHom.mem_ker, AlgHom.id_apply, Ideal.mem_bot]
      calc
        Ideal.span (Set.range (PEmpty.elim : PEmpty → MvPolynomial (Fin 1) A))
            = (⊥ : Ideal (MvPolynomial (Fin 1) A)) := hSpan
        _ = RingHom.ker (MvPolynomial.aeval G.val) := hAevalKer.symm
  }
  let hPFinite : P.IsFinite := {
    finite_vars := inferInstance,
    finite_rels := inferInstance,
  }
  let hQ : Algebra.PreSubmersivePresentation.{0, 0} A (MvPolynomial (Fin 1) A) := {
    toPresentation := P,
    map := PEmpty.elim,
    map_inj := by
      rintro a b h
      cases a
    relations_finite := inferInstance
  }
  letI : Fintype PEmpty := inferInstance
  letI : DecidableEq PEmpty := Classical.decEq _
  have hdet : LinearMap.det hQ.differential = (1 : hQ.Ring) := by
    exact LinearMap.det_eq_one_of_subsingleton (f := hQ.differential)
  let hQS : Algebra.SubmersivePresentation.{0, 0} A (MvPolynomial (Fin 1) A) := {
    toPreSubmersivePresentation := hQ,
    jacobian_isUnit := by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
      have hdetJ : hQ.jacobiMatrix.det = (1 : hQ.Ring) := by
        rw [Matrix.det_isEmpty]
      rw [hdetJ, map_one]
      exact isUnit_one,
    isFinite := by
      change hQ.IsFinite
      exact hPFinite,
  }
  have hdim : P.dimension = 1 := by
    change Nat.card (Fin 1) - Nat.card PEmpty = 1
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    change 1 - Nat.card PEmpty = 1
    rw [Nat.card_eq_fintype_card]
    change 1 - Fintype.card PEmpty = 1
    rw [Fintype.card_pempty, Nat.sub_zero]
  exact ⟨hQS, hdim⟩

theorem polynomial_isStandardSmoothOfRelativeDimension_one
  (R : Type*) [CommRing R] :
    RingHom.IsStandardSmoothOfRelativeDimension.{0, 0} 1
      (Polynomial.C : R →+* Polynomial R) := by
  letI : Algebra R (Polynomial R) := Polynomial.algebraOfAlgebra
  rw [RingHom.IsStandardSmoothOfRelativeDimension]
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial (Fin 1) R) :=
    mvPolynomial_fin_one_isStandardSmoothOfRelativeDimension R
  let e : MvPolynomial (Fin 1) R ≃ₐ[R] Polynomial R :=
    (MvPolynomial.finSuccEquiv R 0).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)))
  have hRel :
      RingHom.IsStandardSmoothOfRelativeDimension.{0, 0} 1
        (algebraMap R (Polynomial R)) :=
    algebra_isStandardSmoothOfRelativeDimension_of_equiv
      (R := R)
      (A := MvPolynomial (Fin 1) R)
      (B := Polynomial R)
      (n := 1)
      e
  exact hRel

end _root_.Algebra

end
