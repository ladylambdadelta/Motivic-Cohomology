import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Exactness.Owner

/-!
# Comparison of explicit and canonical truncation short complexes

This file compares the explicit chosen truncation short complex with the
canonical short complex attached by Mathlib to the distinguished chosen
truncation triangle.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives
namespace TraceAnalyticMotivicTStructure

namespace YonedaTruncationRepresentative

/-- The explicit chosen truncation short complex is isomorphic to the
canonical distinguished short complex attached to the same chosen triangle. -/
def shortComplexIsoDistinguishedShortComplex
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.shortComplex ≅
      representative.distinguishedShortComplex :=
  ShortComplex.isoMk
    (Iso.refl _)
    (Iso.refl _)
    (Iso.refl _)
    (Eq.trans
      (Category.id_comp representative.distinguishedShortComplex.f)
      (Eq.trans
        representative.distinguishedShortComplex_f
        (Eq.trans
          (Eq.symm representative.shortComplex_f)
          (Eq.symm
            (Category.comp_id representative.shortComplex.f)))))
    (Eq.trans
      (Category.id_comp representative.distinguishedShortComplex.g)
      (Eq.trans
        representative.distinguishedShortComplex_g
        (Eq.trans
          (Eq.symm representative.shortComplex_g)
          (Eq.symm
            (Category.comp_id representative.shortComplex.g)))))

/-- The first component of the explicit-to-canonical short-complex
comparison is the identity. -/
theorem shortComplexIsoDistinguishedShortComplex_hom_τ₁
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.shortComplexIsoDistinguishedShortComplex.hom.τ₁ =
      𝟙 _ :=
  rfl

/-- The second component of the explicit-to-canonical short-complex
comparison is the identity. -/
theorem shortComplexIsoDistinguishedShortComplex_hom_τ₂
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.shortComplexIsoDistinguishedShortComplex.hom.τ₂ =
      𝟙 _ :=
  rfl

/-- The third component of the explicit-to-canonical short-complex
comparison is the identity. -/
theorem shortComplexIsoDistinguishedShortComplex_hom_τ₃
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.shortComplexIsoDistinguishedShortComplex.hom.τ₃ =
      𝟙 _ :=
  rfl

/-- The normalized adjacent cut-`1` explicit chosen truncation short complex
is isomorphic to the canonical distinguished short complex. -/
def normalized_shortComplexIsoDistinguishedShortComplex
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object) :
    representative.shortComplex ≅
      representative.distinguishedShortComplex :=
  representative.shortComplexIsoDistinguishedShortComplex

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
