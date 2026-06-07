import Boundary.PolynomialSmoothness.StandardSmoothDimensionZero
import Boundary.PolynomialSmoothness.JacobianTransport
import Mathlib.Algebra.Polynomial.Basic

namespace Boundary
noncomputable section
namespace _root_.Algebra

universe u

example (A : Type u) [CommRing A] :
    Algebra.IsStandardSmoothOfRelativeDimension.{0, 0} 1 A (MvPolynomial (Fin 1) A) := by
  let G : Algebra.Generators A (MvPolynomial (Fin 1) A) := {
    vars := Fin 1,
    val := MvPolynomial.X,
    σ' := fun p => p,
    aeval_val_σ' := by
      intro p
      simpa [MvPolynomial.aeval_X_left] using (rfl : MvPolynomial.aeval MvPolynomial.X p = p),
  }
  let P : Algebra.Presentation A (MvPolynomial (Fin 1) A) := {
    toGenerators := G,
    rels := PEmpty,
    relation := PEmpty.elim,
    span_range_relation_eq_ker := by
      have hSpan : Ideal.span (Set.range (PEmpty.elim : PEmpty → MvPolynomial (Fin 1) A)) = (⊥ : Ideal (MvPolynomial (Fin 1) A)) := by
        have hZero : (Set.range (PEmpty.elim : PEmpty → MvPolynomial (Fin 1) A)) = (∅ : Set (MvPolynomial (Fin 1) A)) := by
          ext x
          constructor
          · rintro ⟨a, rfl⟩
            cases a
          · intro hx
            exact hx
        rw [hZero]
        exact (Ideal.span_empty : Ideal.span (∅ : Set (MvPolynomial (Fin 1) A)) = (⊥ : Ideal (MvPolynomial (Fin 1) A)))
      have hKer : RingHom.ker (AlgHom.id A (MvPolynomial (Fin 1) A)) = (⊥ : Ideal (MvPolynomial (Fin 1) A)) := by
        ext x
        simp [RingHom.mem_ker]
      rw [Algebra.Generators.ker_eq_ker_aeval_val, G, MvPolynomial.aeval_X_left, hSpan, hKer]
  }
  let hPFinite : P.IsFinite := {
    finite_vars := inferInstance,
    finite_rels := inferInstance,
  }
  let hQ : Algebra.PreSubmersivePresentation.{0,0} A (MvPolynomial (Fin 1) A) := {
    toPresentation := P,
    map := PEmpty.elim,
    map_inj := by
      rintro a b h
      cases a
    relations_finite := inferInstance,
  }
  letI : Fintype PEmpty := inferInstance
  letI : DecidableEq PEmpty := Classical.decEq _
  have hdet :
      (MvPolynomial.map (RingHom.id A)) (LinearMap.det hQ.differential) = (1 : MvPolynomial (Fin 1) A) := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det (P := hQ.toPresentation)]
    simp
  let hQS : Algebra.SubmersivePresentation.{0, 0} A (MvPolynomial (Fin 1) A) := {
    toPreSubmersivePresentation := hQ,
    jacobian_isUnit := by
      rw [hdet]
      exact isUnit_one
    isFinite := by
      change P.IsFinite
      simpa [P] using hPFinite
  }
  have hdim : P.dimension = 1 := by
    change Nat.card (Fin 1) - Nat.card PEmpty = 1
    simp
  exact ⟨hQS, hdim⟩

end _root_.Algebra
end Boundary
