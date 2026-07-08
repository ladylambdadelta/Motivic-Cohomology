import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.NullSubcategory.Extension.Owner

/-!
# Nullity criteria for the normalized cone-comparison cone object

This file records the zero-object reduction for the concrete cone object of
the normalized additive cone-to-upper comparison map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- If the normalized cone-comparison cone object is identified with zero,
then it belongs to the stable null subcategory. -/
theorem additiveNormalizedConeComparisonConeObject_null_of_eq_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hzero :
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex = 0) :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex) :=
  Eq.subst
    (motive :=
      fun object =>
        TraceAnalyticStableNullSubcategory.P object)
    (Eq.symm hzero)
    TraceAnalyticStableNullObject.zero_mem

/-- A zero cone object makes the normalized additive cone-to-upper comparison
belong to the Verdier inverted morphism class. -/
theorem additiveNormalizedConeComparisonMap_inverted_of_coneObject_eq_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hzero :
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex = 0) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonMap_inverted_of_coneObject_null
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonConeObject_null_of_eq_zero
          cut
          complex
          hzero)

/-- If the normalized cone-comparison cone object is a zero object, then it
belongs to the stable null subcategory. -/
theorem additiveNormalizedConeComparisonConeObject_null_of_isZero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hzero :
      IsZero
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
          cut
          complex)) :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex) :=
  TraceAnalyticStableNullSubcategory.mem_of_isZero
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
      cut
      complex)
    hzero

/-- A zero-object cone makes the normalized additive cone-to-upper comparison
belong to the Verdier inverted morphism class. -/
theorem additiveNormalizedConeComparisonMap_inverted_of_coneObject_isZero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hzero :
      IsZero
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
          cut
          complex)) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonMap_inverted_of_coneObject_null
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonConeObject_null_of_isZero
          cut
          complex
          hzero)

/-- If the normalized cone-comparison cone object is identified with the middle
vertex of a distinguished extension of stable-null objects, then it belongs to
the stable null subcategory. -/
theorem additiveNormalizedConeComparisonConeObject_null_of_extension
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (coneTriangle : Triangle TraceAnalyticAdditiveHomotopyCategory)
    (coneDistinguished :
      coneTriangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (coneVertexEq :
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
          cut
          complex =
        coneTriangle.obj₂)
    (left : TraceAnalyticStableNullSubcategory.P coneTriangle.obj₁)
    (right : TraceAnalyticStableNullSubcategory.P coneTriangle.obj₃) :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex) :=
  Eq.subst
    (motive :=
      fun object =>
        TraceAnalyticStableNullSubcategory.P object)
    (Eq.symm coneVertexEq)
    (TraceAnalyticStableNullSubcategory.extension_mem
      coneTriangle
      coneDistinguished
      left
      right)

/-- If the normalized cone-comparison cone object is identified with the middle
vertex of a distinguished extension of stable-null objects, then the normalized
cone-to-upper comparison is Verdier-inverted. -/
theorem additiveNormalizedConeComparisonMap_inverted_of_coneObject_extension
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (coneTriangle : Triangle TraceAnalyticAdditiveHomotopyCategory)
    (coneDistinguished :
      coneTriangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (coneVertexEq :
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
          cut
          complex =
        coneTriangle.obj₂)
    (left : TraceAnalyticStableNullSubcategory.P coneTriangle.obj₁)
    (right : TraceAnalyticStableNullSubcategory.P coneTriangle.obj₃) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonMap_inverted_of_coneObject_null
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonConeObject_null_of_extension
          cut
          complex
          coneTriangle
          coneDistinguished
          coneVertexEq
          left
          right)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
