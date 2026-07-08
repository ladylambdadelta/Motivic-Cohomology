import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.BoundedSubcategory.NullHomotopy.BoundedMorphisms.Owner

/-!
# Bounded null-homotopy truncation triangles

This file names the concrete bounded-stable truncation triangle package used
on the path to an internal bounded-stable t-structure.  The package consists
only of bounded stable objects, bounded stable morphisms, the pulled-back
`LE` and `GE` memberships, and the ambient distinguished triangle obtained by
including the bounded morphisms into the analytic comparison source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- A concrete bounded-stable truncation triangle with ambient distinguished
triangle certificate after inclusion into the analytic comparison source. -/
structure NullHomotopyBoundedTriangle
    (middleObject : TraceAnalyticDMgmComparisonSource.BoundedStable) where
  lower : TraceAnalyticDMgmComparisonSource.BoundedStable
  middle : TraceAnalyticDMgmComparisonSource.BoundedStable
  upper : TraceAnalyticDMgmComparisonSource.BoundedStable
  firstMap : lower ⟶ middle
  secondMap : middle ⟶ upper
  connectingMap :
    upper ⟶
      TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedObject lower 1
  middle_eq : middle = middleObject
  lower_mem :
    TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 lower
  upper_mem :
    TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 upper
  ambient_distinguished :
    Triangle.mk
        (TraceAnalyticDMgmComparisonSource.BoundedStable
          .inclusion.map firstMap)
        (TraceAnalyticDMgmComparisonSource.BoundedStable
          .inclusion.map secondMap)
        (TraceAnalyticDMgmComparisonSource.BoundedStable
          .inclusion.map connectingMap) ∈
      TraceAnalyticDMgmComparisonSource.distinguishedTriangles

/-- Null-homotopic cone identities construct the concrete bounded-stable
truncation triangle package. -/
def nullHomotopyBoundedTriangle
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
    TraceAnalyticDMgmComparisonSource.BoundedStable
      .NullHomotopyBoundedTriangle object :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .exists_ambient_triangle_zero_one_boundedMorphisms_of_nullHomotopicIdentity
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
                                (fun lower_mem upperAndDistinguished =>
                                  And.elim
                                    upperAndDistinguished
                                    (fun upper_mem ambient_distinguished =>
                                      {
                                        lower := lower
                                        middle := middle
                                        upper := upper
                                        firstMap := firstMap
                                        secondMap := secondMap
                                        connectingMap := connectingMap
                                        middle_eq := middle_eq
                                        lower_mem := lower_mem
                                        upper_mem := upper_mem
                                        ambient_distinguished :=
                                          ambient_distinguished
                                      }))))))))

/-- The constructed bounded truncation triangle has the requested middle
object. -/
theorem nullHomotopyBoundedTriangle_middle_eq
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
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .nullHomotopyBoundedTriangle object nullHomotopicIdentity).middle =
      object :=
  (TraceAnalyticDMgmComparisonSource.BoundedStable
    .nullHomotopyBoundedTriangle object nullHomotopicIdentity).middle_eq

/-- The constructed bounded truncation triangle has a lower vertex in
`LE 0`. -/
theorem nullHomotopyBoundedTriangle_lower_mem
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
    TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE
      0
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .nullHomotopyBoundedTriangle object nullHomotopicIdentity).lower :=
  (TraceAnalyticDMgmComparisonSource.BoundedStable
    .nullHomotopyBoundedTriangle object nullHomotopicIdentity).lower_mem

/-- The constructed bounded truncation triangle has an upper vertex in
`GE 1`. -/
theorem nullHomotopyBoundedTriangle_upper_mem
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
    TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE
      1
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .nullHomotopyBoundedTriangle object nullHomotopicIdentity).upper :=
  (TraceAnalyticDMgmComparisonSource.BoundedStable
    .nullHomotopyBoundedTriangle object nullHomotopicIdentity).upper_mem

/-- The constructed bounded truncation triangle is ambient distinguished after
including its bounded morphisms into the analytic comparison source. -/
theorem nullHomotopyBoundedTriangle_ambient_distinguished
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
    Triangle.mk
        (TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
          (TraceAnalyticDMgmComparisonSource.BoundedStable
            .nullHomotopyBoundedTriangle
              object
              nullHomotopicIdentity).firstMap)
        (TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
          (TraceAnalyticDMgmComparisonSource.BoundedStable
            .nullHomotopyBoundedTriangle
              object
              nullHomotopicIdentity).secondMap)
        (TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
          (TraceAnalyticDMgmComparisonSource.BoundedStable
            .nullHomotopyBoundedTriangle
              object
              nullHomotopicIdentity).connectingMap) ∈
      TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  (TraceAnalyticDMgmComparisonSource.BoundedStable
    .nullHomotopyBoundedTriangle object nullHomotopicIdentity)
    .ambient_distinguished

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
