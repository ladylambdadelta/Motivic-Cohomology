import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.BoundedSubcategory.NullHomotopy.BoundedTriangle.Owner

/-!
# Bounded null-homotopy truncation triangle projections

This file exposes the concrete bounded truncation triangle package as a
single field-shaped existential.  Downstream Mathlib-facing truncation work can
consume this theorem without reopening the construction of the lower object,
upper object, bounded morphisms, or ambient distinguished triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- Any concrete bounded null-homotopy truncation triangle carries exactly the
field data needed for the bounded-stable truncation package. -/
theorem NullHomotopyBoundedTriangle.fields
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
    (triangle :
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .NullHomotopyBoundedTriangle object) :
    triangle.middle = object ∧
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE
        0
        triangle.lower ∧
        TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE
          1
          triangle.upper ∧
          Triangle.mk
              (TraceAnalyticDMgmComparisonSource.BoundedStable
                .inclusion.map triangle.firstMap)
              (TraceAnalyticDMgmComparisonSource.BoundedStable
                .inclusion.map triangle.secondMap)
              (TraceAnalyticDMgmComparisonSource.BoundedStable
                .inclusion.map triangle.connectingMap) ∈
            TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  And.intro
    triangle.middle_eq
    (And.intro
      triangle.lower_mem
      (And.intro
        triangle.upper_mem
        triangle.ambient_distinguished))

/-- Null-homotopic cone identities produce a bounded truncation triangle
package together with all of its field data. -/
theorem exists_nullHomotopyBoundedTriangle_with_fields
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
    ∃ triangle :
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .NullHomotopyBoundedTriangle object,
      triangle.middle = object ∧
        TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE
          0
          triangle.lower ∧
          TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE
            1
            triangle.upper ∧
            Triangle.mk
                (TraceAnalyticDMgmComparisonSource.BoundedStable
                  .inclusion.map triangle.firstMap)
                (TraceAnalyticDMgmComparisonSource.BoundedStable
                  .inclusion.map triangle.secondMap)
                (TraceAnalyticDMgmComparisonSource.BoundedStable
                  .inclusion.map triangle.connectingMap) ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  let triangle :=
    TraceAnalyticDMgmComparisonSource.BoundedStable
      .nullHomotopyBoundedTriangle object nullHomotopicIdentity
  Exists.intro
    triangle
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .NullHomotopyBoundedTriangle.fields object triangle)

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
