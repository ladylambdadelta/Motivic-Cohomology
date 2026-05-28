import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.RingHom.StandardSmooth

universe u

namespace Boundary

noncomputable section

variable {k : Type u} [Field k]

private noncomputable def polynomialPresentation (k : Type u) [Field k] :
    Algebra.Presentation k (Polynomial k) where
  toGenerators :=
    { vars := PUnit
      val := fun _ => Polynomial.X
      σ' := fun s => Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X PUnit.unit) s
      aeval_val_σ' := by
        intro s
        simpa [MvPolynomial.pUnitAlgEquiv] using (MvPolynomial.pUnitAlgEquiv k).apply_symm_apply s }
  rels := PEmpty
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    simp only [Set.range_eq_empty, Ideal.span_empty]
    symm
    rw [← RingHom.injective_iff_ker_eq_bot]
    simpa [MvPolynomial.pUnitAlgEquiv] using (MvPolynomial.pUnitAlgEquiv k).injective

private instance polynomialPresentation_isFinite (k : Type u) [Field k] :
    (polynomialPresentation k).IsFinite where
  finite_vars := by
    change Finite PUnit
    infer_instance
  finite_rels := by
    change Finite PEmpty
    infer_instance

private noncomputable def polynomialPreSubmersivePresentation (k : Type u) [Field k] :
    Algebra.PreSubmersivePresentation k (Polynomial k) where
  toPresentation := polynomialPresentation k
  map := PEmpty.elim
  map_inj := by
    intro a
    exact PEmpty.elim a
  relations_finite := by
    change Finite PEmpty
    infer_instance

private instance polynomialPreSubmersivePresentation_isFinite (k : Type u) [Field k] :
    (polynomialPreSubmersivePresentation k).IsFinite where
  finite_vars := by
    change Finite PUnit
    infer_instance
  finite_rels := by
    change Finite PEmpty
    infer_instance

private noncomputable def polynomialSubmersivePresentation (k : Type u) [Field k] :
    Algebra.SubmersivePresentation k (Polynomial k) where
  __ := polynomialPreSubmersivePresentation k
  jacobian_isUnit := by
    classical
    letI : Fintype (polynomialPreSubmersivePresentation k).rels := by
      change Fintype PEmpty
      infer_instance
    letI : DecidableEq (polynomialPreSubmersivePresentation k).rels := inferInstance
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [polynomialPreSubmersivePresentation, polynomialPresentation]
  isFinite := polynomialPreSubmersivePresentation_isFinite k

private theorem polynomial_isStandardSmooth (k : Type u) [Field k] :
    Algebra.IsStandardSmooth k (Polynomial k) :=
  ⟨⟨polynomialSubmersivePresentation k⟩⟩

theorem polynomial_C_toAlgebra_eq (k : Type u) [Field k] :
    (Polynomial.C : k →+* Polynomial k).toAlgebra = Polynomial.algebraOfAlgebra := by
  apply Algebra.algebra_ext
  intro r
  rfl

theorem polynomial_C_isStandardSmooth (k : Type u) [Field k] :
    RingHom.IsStandardSmooth (Polynomial.C : k →+* Polynomial k) := by
  rw [RingHom.IsStandardSmooth, polynomial_C_toAlgebra_eq]
  exact polynomial_isStandardSmooth k

end

end Boundary
