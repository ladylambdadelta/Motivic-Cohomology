import Mathlib.CategoryTheory.Triangulated.Yoneda
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.ShortComplex.Owner

/-!
# Yoneda exactness for chosen Yoneda truncation triangles

This file proves the exactness facts supplied by the canonical short complex
that Mathlib attaches to the distinguished chosen truncation triangle of a
concrete Yoneda representative.  These are the hom-level exactness statements
used by the t-structure orthogonality and truncation calculus.
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

/-- The canonical short complex attached by Mathlib to the distinguished
chosen truncation triangle. -/
def distinguishedShortComplex
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    ShortComplex TraceAnalyticDerivedMotiveCategory :=
  Pretriangulated.shortComplexOfDistTriangle
    representative.triangle
    representative.triangle_distinguished

/-- The first object of the canonical distinguished short complex is the
chosen lower object. -/
theorem distinguishedShortComplex_X₁
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.distinguishedShortComplex.X₁ =
      representative.lowerObject :=
  rfl

/-- The middle object of the canonical distinguished short complex is the
represented object. -/
theorem distinguishedShortComplex_X₂
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.distinguishedShortComplex.X₂ = object :=
  rfl

/-- The third object of the canonical distinguished short complex is the
chosen upper object. -/
theorem distinguishedShortComplex_X₃
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.distinguishedShortComplex.X₃ =
      representative.upperObject :=
  rfl

/-- The first map of the canonical distinguished short complex is the chosen
first truncation map. -/
theorem distinguishedShortComplex_f
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.distinguishedShortComplex.f =
      representative.firstMap :=
  rfl

/-- The second map of the canonical distinguished short complex is the chosen
second truncation map. -/
theorem distinguishedShortComplex_g
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.distinguishedShortComplex.g =
      representative.secondMap :=
  rfl

/-- Covariant preadditive Yoneda sends the canonical distinguished truncation
short complex to an exact short complex of abelian groups. -/
theorem coyonedaDistinguishedShortComplex_exact
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object)
    (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ) :
    (representative.distinguishedShortComplex.map
      (preadditiveCoyoneda.obj probe)).Exact :=
  (preadditiveCoyoneda.obj probe).map_distinguished_exact
    representative.triangle
    representative.triangle_distinguished

/-- Contravariant preadditive Yoneda sends the opposite canonical
distinguished truncation short complex to an exact short complex of abelian
groups. -/
theorem yonedaDistinguishedShortComplex_exact
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object)
    (probe : TraceAnalyticDerivedMotiveCategory) :
    (representative.distinguishedShortComplex.op.map
      (preadditiveYoneda.obj probe)).Exact :=
  Pretriangulated.preadditiveYoneda_map_distinguished
    representative.triangle
    representative.triangle_distinguished
    probe

/-- Covariant preadditive Yoneda exactness for the normalized adjacent
cut-`1` canonical distinguished truncation short complex. -/
theorem normalized_coyonedaDistinguishedShortComplex_exact
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ) :
    (representative.distinguishedShortComplex.map
      (preadditiveCoyoneda.obj probe)).Exact :=
  representative.coyonedaDistinguishedShortComplex_exact probe

/-- Contravariant preadditive Yoneda exactness for the normalized adjacent
cut-`1` canonical distinguished truncation short complex. -/
theorem normalized_yonedaDistinguishedShortComplex_exact
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (probe : TraceAnalyticDerivedMotiveCategory) :
    (representative.distinguishedShortComplex.op.map
      (preadditiveYoneda.obj probe)).Exact :=
  representative.yonedaDistinguishedShortComplex_exact probe

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
