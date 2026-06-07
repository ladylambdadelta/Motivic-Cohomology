import Boundary.PolynomialSmoothness.StandardSmoothDimensionZero
import Boundary.PolynomialSmoothness.StandardSmoothTransport
import Boundary.PolynomialSmoothness.JacobianTransport
import Boundary.PolynomialSmoothness.StandardSmoothPolynomialOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Smooth.StandardSmooth

namespace Boundary

noncomputable section

namespace _root_.Algebra

open scoped Polynomial

theorem mvPolynomial_fin_isStandardSmoothOfRelativeDimension
    (R : Type*) [CommRing R] :
    ∀ n : ℕ,
      RingHom.IsStandardSmoothOfRelativeDimension.{0, 0} n
        (algebraMap R (MvPolynomial (Fin n) R)) := by
  intro n
  induction n with
  | zero =>
      letI : Algebra.IsStandardSmoothOfRelativeDimension 0 R R :=
        Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective
          (R := R) (S := R) Function.bijective_id
      exact
        algebra_isStandardSmoothOfRelativeDimension_of_equiv
          (R := R)
          (A := R)
          (B := MvPolynomial (Fin 0) R)
          (n := 0)
          (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm
  | succ n ih =>
      letI : Algebra R (MvPolynomial (Fin n) R) := MvPolynomial.algebra
      have hA0 :
          @Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R)
            _ _ ((algebraMap R (MvPolynomial (Fin n) R)).toAlgebra) :=
        ih.toAlgebra
      have hA :
          @Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R)
            _ _ MvPolynomial.algebra := by
        exact
          Eq.mp
            (congrArg
              (fun A =>
                @Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R)
                  _ _ A)
              (by
                change (MvPolynomial.C : R →+* MvPolynomial (Fin n) R).toAlgebra =
                  MvPolynomial.algebra
                exact mvPolynomial_C_toAlgebra_eq R (Fin n)))
            hA0
      letI : Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := hA
      have hStep0 :
          @Algebra.IsStandardSmoothOfRelativeDimension 1 (MvPolynomial (Fin n) R)
            (Polynomial (MvPolynomial (Fin n) R)) _ _ ((Polynomial.C :
              MvPolynomial (Fin n) R →+* Polynomial (MvPolynomial (Fin n) R)).toAlgebra) :=
        (polynomial_isStandardSmoothOfRelativeDimension_one
          (MvPolynomial (Fin n) R)).toAlgebra
      letI : Algebra (MvPolynomial (Fin n) R) (Polynomial (MvPolynomial (Fin n) R)) :=
        Polynomial.algebraOfAlgebra
      have hStep :
          @Algebra.IsStandardSmoothOfRelativeDimension 1 (MvPolynomial (Fin n) R)
            (Polynomial (MvPolynomial (Fin n) R)) _ _ Polynomial.algebraOfAlgebra := by
        exact
          Eq.mp
            (congrArg
              (fun A =>
                @Algebra.IsStandardSmoothOfRelativeDimension 1 (MvPolynomial (Fin n) R)
                  (Polynomial (MvPolynomial (Fin n) R)) _ _ A)
              (polynomial_C_toAlgebra_eq (MvPolynomial (Fin n) R)))
            hStep0
      letI : Algebra.IsStandardSmoothOfRelativeDimension 1 (MvPolynomial (Fin n) R)
          (Polynomial (MvPolynomial (Fin n) R)) := hStep
      have hTrans :
          Algebra.IsStandardSmoothOfRelativeDimension (n + 1) R
            (Polynomial (MvPolynomial (Fin n) R)) := by
        rw [Nat.add_comm]
        exact Algebra.IsStandardSmoothOfRelativeDimension.trans
          (R := R) (S := MvPolynomial (Fin n) R)
          (T := Polynomial (MvPolynomial (Fin n) R))
          (n := n) (m := 1)
      letI : Algebra.IsStandardSmoothOfRelativeDimension (n + 1) R
          (Polynomial (MvPolynomial (Fin n) R)) := hTrans
      let e : Polynomial (MvPolynomial (Fin n) R) ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
        (MvPolynomial.finSuccEquiv R n).symm
      exact
        algebra_isStandardSmoothOfRelativeDimension_of_equiv
          (R := R)
          (A := Polynomial (MvPolynomial (Fin n) R))
          (B := MvPolynomial (Fin (n + 1)) R)
          (n := n + 1)
          e

end _root_.Algebra

end

end Boundary
