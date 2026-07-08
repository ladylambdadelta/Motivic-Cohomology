import Mathlib.CategoryTheory.Triangulated.Functor
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.HasShift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.BoundedSubcategory.NullHomotopy.BoundedTriangle.Projections.Owner

/-!
# Distinguished triangles in the bounded stable source

This file names the concrete bounded-stable distinguished-triangle predicate:
a bounded triangle is distinguished exactly when its image under the full
subcategory inclusion is distinguished in the ambient analytic comparison
source.  This is the owner-level predicate for the eventual bounded
pretriangulated structure.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The image of a bounded-stable triangle under the inclusion into the
ambient analytic comparison source. -/
def ambientTriangle
    (triangle :
      Triangle TraceAnalyticDMgmComparisonSource.BoundedStable) :
    Triangle TraceAnalyticDMgmComparisonSource :=
  Triangle.mk
    (TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      triangle.mor₁)
    (TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      triangle.mor₂)
    (TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      triangle.mor₃)

/-- The explicit ambient triangle agrees with Mathlib's triangle map for the
bounded-stable inclusion. -/
theorem ambientTriangle_eq_mapTriangle_obj
    (triangle :
      Triangle TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.ambientTriangle triangle =
      (TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion)
        .mapTriangle.obj triangle :=
  rfl

/-- A bounded-stable triangle is distinguished when its image under inclusion
is distinguished in the ambient analytic comparison source. -/
def distinguishedTriangles
    (triangle :
      Triangle TraceAnalyticDMgmComparisonSource.BoundedStable) :
    Prop :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.ambientTriangle triangle ∈
    TraceAnalyticDMgmComparisonSource.distinguishedTriangles

/-- Membership in the bounded distinguished-triangle predicate is exactly
ambient distinguishedness after inclusion. -/
theorem distinguishedTriangles_iff_ambient
    (triangle :
      Triangle TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.distinguishedTriangles
        triangle ↔
      TraceAnalyticDMgmComparisonSource.BoundedStable.ambientTriangle
          triangle ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  Iff.rfl

/-- Ambient distinguishedness after inclusion gives bounded distinguishedness. -/
theorem distinguishedTriangles_of_ambient
    (triangle :
      Triangle TraceAnalyticDMgmComparisonSource.BoundedStable)
    (ambientDistinguished :
      TraceAnalyticDMgmComparisonSource.BoundedStable.ambientTriangle
          triangle ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.distinguishedTriangles
      triangle :=
  ambientDistinguished

/-- Bounded distinguished triangles are closed under triangle isomorphism,
because their ambient images are closed under triangle isomorphism. -/
theorem distinguishedTriangles_isomorphic
    {source target :
      Triangle TraceAnalyticDMgmComparisonSource.BoundedStable}
    (sourceDistinguished :
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .distinguishedTriangles source)
    (triangleIso : target ≅ source) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.distinguishedTriangles
      target :=
  Pretriangulated.isomorphic_distinguished
    (TraceAnalyticDMgmComparisonSource.BoundedStable.ambientTriangle source)
    sourceDistinguished
    (TraceAnalyticDMgmComparisonSource.BoundedStable.ambientTriangle target)
    ((TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion)
      .mapTriangle.mapIso triangleIso)

/-- Bounded-stable contractible triangles are distinguished because their
ambient images are the ambient contractible triangles. -/
theorem distinguishedTriangles_contractible
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.distinguishedTriangles
      (contractibleTriangle object) :=
  Pretriangulated.contractible_distinguished object.object

/-- The bounded triangle carried by a concrete null-homotopy truncation
package. -/
def NullHomotopyBoundedTriangle.triangle
    {object : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (package :
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .NullHomotopyBoundedTriangle object) :
    Triangle TraceAnalyticDMgmComparisonSource.BoundedStable :=
  Triangle.mk
    package.firstMap
    package.secondMap
    package.connectingMap

/-- The bounded triangle extracted from a null-homotopy truncation package is
distinguished in the bounded-stable distinguished-triangle predicate. -/
theorem NullHomotopyBoundedTriangle.triangle_distinguished
    {object : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (package :
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .NullHomotopyBoundedTriangle object) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.distinguishedTriangles
      package.triangle :=
  package.ambient_distinguished

/-- Null-homotopic cone identities produce a bounded-stable distinguished
triangle whose lower and upper vertices lie in the adjacent aisle and
coaisle. -/
theorem exists_distinguishedTriangle_zero_one_of_nullHomotopicIdentity
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
    ∃ package :
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .NullHomotopyBoundedTriangle object,
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE
        0
        package.lower ∧
        TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE
          1
          package.upper ∧
          TraceAnalyticDMgmComparisonSource.BoundedStable
            .distinguishedTriangles package.triangle :=
  let package :=
    TraceAnalyticDMgmComparisonSource.BoundedStable
      .nullHomotopyBoundedTriangle object nullHomotopicIdentity
  Exists.intro
    package
    (And.intro
      package.lower_mem
      (And.intro
        package.upper_mem
        package.triangle_distinguished))

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
