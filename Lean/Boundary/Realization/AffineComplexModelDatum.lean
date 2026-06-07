import Boundary.Realization.AffinePresentation
import Boundary.Realization.AffineComplexPolynomials

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Boundary
namespace Realization

/-- For an affine open in a smooth finite-type `ℂ`-scheme, there exists a finite family of
polynomials whose common zero set is a closed subset of `ℂⁿ` and whose span cuts out the relation
ideal of the affine coordinate ring presentation. -/
theorem smAffineOpenSections_exists_closed_complexEquationModel
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    ∃ (n m : ℕ) (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(X.scheme, (U : X.scheme.Opens)))
      (p : Fin m → MvPolynomial (Fin n) ℂ),
      Function.Surjective f ∧
        Ideal.span (Set.range p) = RingHom.ker f ∧
        IsClosed (finitePolynomialZeroSet p) := by
  obtain ⟨n, m, f, p, hf, hp⟩ :=
    smAffineOpenSections_finiteEquationsAlgHom_baseField (k := ℂ) X U
  exact ⟨n, m, f, p, hf, hp, isClosed_finitePolynomialZeroSet p⟩

/-- Chosen finite polynomial presentation data for the canonical complex model of an affine open. -/
structure smAffineOpenComplexModelDatum
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) where
  varCount : ℕ
  equationCount : ℕ
  presentation : MvPolynomial (Fin varCount) ℂ →ₐ[ℂ] Γ(X.scheme, (U : X.scheme.Opens))
  equations : Fin equationCount → MvPolynomial (Fin varCount) ℂ
  presentation_surjective : Function.Surjective presentation
  equations_span : Ideal.span (Set.range equations) = RingHom.ker presentation.toRingHom

/-- The chosen finite polynomial model datum attached to an affine open. -/
theorem smAffineOpenComplexModelDatum_exists
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    Nonempty (smAffineOpenComplexModelDatum X U) := by
  classical
  rcases smAffineOpenSections_exists_closed_complexEquationModel (X := X) (U := U) with
    ⟨n, m, f, p, hf, hp, _⟩
  exact ⟨
    { varCount := n
      equationCount := m
      presentation := f
      equations := p
      presentation_surjective := hf
      equations_span := hp }⟩

/-- The chosen finite polynomial model datum attached to an affine open. -/
noncomputable def smAffineOpenComplexModelDatumOf
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    smAffineOpenComplexModelDatum X U :=
  Classical.choice (smAffineOpenComplexModelDatum_exists (X := X) (U := U))

/-- Chosen number of variables for the canonical complex model of an affine open. -/
noncomputable def smAffineOpenComplexModelVarCount
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) : ℕ :=
  (smAffineOpenComplexModelDatumOf X U).varCount

/-- Chosen number of defining equations for the canonical complex model of an affine open. -/
noncomputable def smAffineOpenComplexModelEquationCount
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) : ℕ :=
  (smAffineOpenComplexModelDatumOf X U).equationCount

/-- Chosen finite polynomial presentation of an affine open. -/
noncomputable def smAffineOpenComplexModelPresentation
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    MvPolynomial (Fin (smAffineOpenComplexModelVarCount X U)) ℂ →ₐ[ℂ]
      Γ(X.scheme, (U : X.scheme.Opens)) :=
  (smAffineOpenComplexModelDatumOf X U).presentation

/-- Chosen defining equations for the canonical complex model of an affine open. -/
noncomputable def smAffineOpenComplexModelEquations
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    Fin (smAffineOpenComplexModelEquationCount X U) →
      MvPolynomial (Fin (smAffineOpenComplexModelVarCount X U)) ℂ :=
  (smAffineOpenComplexModelDatumOf X U).equations

/-- Surjectivity of the chosen affine polynomial presentation. -/
theorem smAffineOpenComplexModelPresentation_surjective
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    Function.Surjective (smAffineOpenComplexModelPresentation X U) :=
  (smAffineOpenComplexModelDatumOf X U).presentation_surjective

/-- The defining equations span the kernel of the chosen affine polynomial presentation. -/
theorem smAffineOpenComplexModelEquations_span
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    Ideal.span (Set.range (smAffineOpenComplexModelEquations X U)) =
      RingHom.ker (smAffineOpenComplexModelPresentation X U).toRingHom :=
  (smAffineOpenComplexModelDatumOf X U).equations_span

/-- The canonical complex model of an affine open, defined by its chosen equations. -/
abbrev smAffineOpenComplexModel
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    Type :=
  finitePolynomialZeroSet (smAffineOpenComplexModelEquations X U)

end Realization
end Boundary
