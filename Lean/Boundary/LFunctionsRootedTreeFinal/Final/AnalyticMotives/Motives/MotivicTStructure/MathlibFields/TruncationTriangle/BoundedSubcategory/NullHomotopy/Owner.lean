import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.BoundedSubcategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Fields.ConeComparison.ContractibleCone.NullHomotopy.Owner

/-!
# Null-homotopy truncation triangles for bounded stable source objects

This file specializes the bounded-stable ambient truncation theorem to the
null-homotopic identity criterion for the normalized cone-comparison field.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- Every bounded stable source object has the ambient Mathlib-shaped
truncation triangle once the normalized cone-to-upper mapping cones have
null-homotopic identities. -/
theorem exists_ambient_triangle_zero_one_of_nullHomotopicIdentity
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∃ hom :
          ∀ i j,
            (ComplexShape.up ℤ).Rel j i →
              (CochainComplex.mappingCone
                (TraceAnalyticMotivicTStructure
                  .additiveNormalizedConeComparisonCochainMap
                    0
                    complex.complex)).X i ⟶
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      0
                      complex.complex)).X j,
          𝟙
              (CochainComplex.mappingCone
                (TraceAnalyticMotivicTStructure
                  .additiveNormalizedConeComparisonCochainMap
                    0
                    complex.complex)) =
            _root_.HomologicalComplex.nullHomotopicMap' hom) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
        TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object.object)
            (secondMap : object.object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .tStructure_exists_triangle_zero_one_of_boundedStableObject_of_nullHomotopicIdentity
      object.membership
      homology
      nullHomotopicIdentity

/-- Every bounded stable source object has the ambient Mathlib-shaped
truncation triangle, in the exact `TStructure.exists_triangle_zero_one` field
order, once the normalized cone-to-upper mapping cones have null-homotopic
identities. -/
theorem exists_ambient_triangle_zero_one_fieldShape_of_nullHomotopicIdentity
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∃ hom :
          ∀ i j,
            (ComplexShape.up ℤ).Rel j i →
              (CochainComplex.mappingCone
                (TraceAnalyticMotivicTStructure
                  .additiveNormalizedConeComparisonCochainMap
                    0
                    complex.complex)).X i ⟶
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      0
                      complex.complex)).X j,
          𝟙
              (CochainComplex.mappingCone
                (TraceAnalyticMotivicTStructure
                  .additiveNormalizedConeComparisonCochainMap
                    0
                    complex.complex)) =
            _root_.HomologicalComplex.nullHomotopicMap' hom) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ : TraceAnalyticMotivicTStructure.mathlibLE 0 lower)
      (_ : TraceAnalyticMotivicTStructure.mathlibGE 1 upper)
      (firstMap : lower ⟶ object.object)
      (secondMap : object.object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .tStructure_exists_triangle_zero_one_fieldShape_of_nullHomotopicIdentity
      object.membership
      homology
      nullHomotopicIdentity

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
