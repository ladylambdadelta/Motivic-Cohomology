import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.FromDegreewise.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Subcategories.Decomposition.Owner

/-!
# Homological-subcategory truncation decomposition from degreewise exactness

This file gives the direct degreewise-exact entry point for the derived
truncation triangle whose first and third vertices are exposed as aisle and
coaisle objects.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The lower aisle vertex obtained from degreewise exactness of the analytic
Yoneda truncation sequence. -/
def abelianEnvelopeCochainDecompositionDerivedLowerAisleObjectOfDegreewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangleLowerAisleObject
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
          cut
          complex
          hdegree)

/-- The upper coaisle vertex obtained from degreewise exactness of the analytic
Yoneda truncation sequence. -/
def abelianEnvelopeCochainDecompositionDerivedUpperCoaisleObjectOfDegreewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangleUpperCoaisleObject
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
          cut
          complex
          hdegree)

/-- The subcategory-exposed truncation triangle obtained directly from
degreewise exactness. -/
def abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangleOfDegreewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    Triangle TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
          cut
          complex
          hdegree)

/-- The degreewise subcategory-exposed truncation triangle is the
subcategory-exposed triangle for the assembled cochain short exactness
witness. -/
theorem abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangleOfDegreewise_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangleOfDegreewise
          cut
          complex
          hdegree =
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle
          cut
          complex
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
              cut
              complex
              hdegree) :=
  rfl

/-- Degreewise exactness gives a distinguished derived analytic truncation
triangle whose first and third vertices are exposed through the aisle and
coaisle inclusions. -/
theorem abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangleOfDegreewise_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangleOfDegreewise
          cut
          complex
          hdegree ∈
      distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle_distinguished
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
          cut
          complex
          hdegree)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
