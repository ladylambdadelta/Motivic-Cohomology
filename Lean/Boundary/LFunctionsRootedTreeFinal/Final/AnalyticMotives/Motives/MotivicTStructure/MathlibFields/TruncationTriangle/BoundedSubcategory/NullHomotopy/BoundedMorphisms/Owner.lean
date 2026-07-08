import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.BoundedSubcategory.NullHomotopy.BoundedVertices.Owner

/-!
# Bounded morphisms for null-homotopy truncation triangles

This file packages the three morphisms in the bounded-vertex null-homotopy
truncation triangle as morphisms of the bounded stable full subcategory.  The
ambient distinguished triangle statement is retained on the included objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- Null-homotopic cone identities give a bounded-vertex truncation triangle
whose first, second, and connecting maps are morphisms in the bounded stable
full subcategory. -/
theorem exists_ambient_triangle_zero_one_boundedMorphisms_of_nullHomotopicIdentity
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
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
    ∃ (lower middle upper : TraceAnalyticDMgmComparisonSource.BoundedStable)
      (firstMap : lower ⟶ middle)
      (secondMap : middle ⟶ upper)
      (connectingMap :
        upper ⟶
          TraceAnalyticDMgmComparisonSource.BoundedStable
            .shiftedObject lower 1),
      middle = object ∧
        TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 lower ∧
          TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 upper ∧
            Triangle.mk
                (TraceAnalyticDMgmComparisonSource.BoundedStable
                  .inclusion.map firstMap)
                (TraceAnalyticDMgmComparisonSource.BoundedStable
                  .inclusion.map secondMap)
                (TraceAnalyticDMgmComparisonSource.BoundedStable
                  .inclusion.map connectingMap) ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .exists_ambient_triangle_zero_one_boundedVertices_fieldShape_of_nullHomotopicIdentity
        object
        nullHomotopicIdentity)
    (fun lower lowerData =>
      Exists.elim
        lowerData
        (fun middle middleData =>
          Exists.elim
            middleData
            (fun upper upperData =>
              Exists.elim
                upperData
                (fun firstMap firstMapData =>
                  Exists.elim
                    firstMapData
                    (fun secondMap secondMapData =>
                      Exists.elim
                        secondMapData
                        (fun connectingMap remainingData =>
                          And.elim
                            remainingData
                            (fun middle_eq membershipData =>
                              And.elim
                                membershipData
                                (fun lowerMembership upperAndTriangle =>
                                  And.elim
                                    upperAndTriangle
                                    (fun upperMembership triangle_mem =>
                                      Exists.intro
                                        lower
                                        (Exists.intro
                                          middle
                                          (Exists.intro
                                            upper
                                            (Exists.intro
                                              firstMap
                                              (Exists.intro
                                                secondMap
                                                (Exists.intro
                                                  connectingMap
                                                  (And.intro
                                                    middle_eq
                                                    (And.intro
                                                      lowerMembership
                                                      (And.intro
                                                        upperMembership
                                                        triangle_mem))))))))))))))))

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
