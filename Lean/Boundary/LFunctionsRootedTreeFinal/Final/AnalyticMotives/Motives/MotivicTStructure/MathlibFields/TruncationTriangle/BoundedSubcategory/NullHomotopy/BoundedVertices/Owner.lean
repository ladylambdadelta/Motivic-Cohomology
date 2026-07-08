import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Assembly.HomologyDischarged.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSource.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.TruncationTriangle.BoundedSubcategory.NullHomotopy.Owner

/-!
# Bounded vertices for null-homotopy truncation triangles

This file upgrades the ambient null-homotopy truncation triangle for a bounded
stable source object by packaging its lower and upper vertices as bounded
stable source objects.  The triangle itself is still the ambient distinguished
triangle; this is the owner step that removes the false need for global
boundedness of every object in the comparison source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The lower vertex in a Mathlib-facing ambient truncation triangle is a
bounded stable source object. -/
def lowerVertexOfMathlibLE
    {lower : TraceAnalyticDMgmComparisonSource}
    (membership : TraceAnalyticMotivicTStructure.mathlibLE 0 lower) :
    TraceAnalyticDMgmComparisonSource.BoundedStable where
  obj := lower
  property :=
    TraceAnalyticMotivicTStructure
      .boundedStableObject_of_mathlibLE 0 membership

/-- The upper vertex in a Mathlib-facing ambient truncation triangle is a
bounded stable source object. -/
def upperVertexOfMathlibGE
    {upper : TraceAnalyticDMgmComparisonSource}
    (membership : TraceAnalyticMotivicTStructure.mathlibGE 1 upper) :
    TraceAnalyticDMgmComparisonSource.BoundedStable where
  obj := upper
  property :=
    TraceAnalyticMotivicTStructure
      .boundedStableObject_of_mathlibGE 1 membership

/-- The packaged lower vertex has the original ambient object. -/
theorem lowerVertexOfMathlibLE_object
    {lower : TraceAnalyticDMgmComparisonSource}
    (membership : TraceAnalyticMotivicTStructure.mathlibLE 0 lower) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .lowerVertexOfMathlibLE membership).object =
      lower :=
  rfl

/-- The packaged upper vertex has the original ambient object. -/
theorem upperVertexOfMathlibGE_object
    {upper : TraceAnalyticDMgmComparisonSource}
    (membership : TraceAnalyticMotivicTStructure.mathlibGE 1 upper) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .upperVertexOfMathlibGE membership).object =
      upper :=
  rfl

/-- Null-homotopic cone identities give a truncation triangle for a bounded
stable source object whose lower and upper vertices are also bounded stable
source objects. -/
theorem exists_ambient_triangle_zero_one_boundedVertices_of_nullHomotopicIdentity
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
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource.BoundedStable)
      (firstMap : lower.object ⟶ object.object)
      (secondMap : object.object ⟶ upper.object)
      (connectingMap : upper.object ⟶ lower.object⟦(1 : ℤ)⟧),
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 lower ∧
        TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 upper ∧
          Triangle.mk firstMap secondMap connectingMap ∈
            TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .exists_ambient_triangle_zero_one_fieldShape_of_nullHomotopicIdentity
        object
        (fun complex =>
          TraceAnalyticMotivicTStructure
            .sourceComplexWeightBoundedBy_hasHomology complex)
        nullHomotopicIdentity)
    (fun lower lowerData =>
      Exists.elim
        lowerData
        (fun upper upperData =>
          Exists.elim
            upperData
            (fun lowerMembership lowerMembershipData =>
              Exists.elim
                lowerMembershipData
                (fun upperMembership upperMembershipData =>
                  Exists.elim
                    upperMembershipData
                    (fun firstMap firstMapData =>
                      Exists.elim
                        firstMapData
                        (fun secondMap secondMapData =>
                          Exists.elim
                            secondMapData
                            (fun connectingMap triangle_mem =>
                              Exists.intro
                                (TraceAnalyticDMgmComparisonSource
                                  .BoundedStable
                                  .lowerVertexOfMathlibLE lowerMembership)
                                (Exists.intro
                                  (TraceAnalyticDMgmComparisonSource
                                    .BoundedStable
                                    .upperVertexOfMathlibGE upperMembership)
                                  (Exists.intro
                                    firstMap
                                    (Exists.intro
                                      secondMap
                                      (Exists.intro
                                        connectingMap
                                        (And.intro
                                          lowerMembership
                                          (And.intro
                                            upperMembership
                                            triangle_mem)))))))))))))

/-- Field-shaped bounded-vertex form of the null-homotopy truncation triangle:
the lower, middle, and upper displayed objects are all bounded stable source
objects, the middle object is the input object, and the distinguished triangle
is the ambient analytic comparison-source triangle. -/
theorem exists_ambient_triangle_zero_one_boundedVertices_fieldShape_of_nullHomotopicIdentity
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
      (firstMap : lower.object ⟶ middle.object)
      (secondMap : middle.object ⟶ upper.object)
      (connectingMap : upper.object ⟶ lower.object⟦(1 : ℤ)⟧),
      middle = object ∧
        TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE 0 lower ∧
          TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE 1 upper ∧
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .exists_ambient_triangle_zero_one_boundedVertices_of_nullHomotopicIdentity
        object
        nullHomotopicIdentity)
    (fun lower lowerData =>
      Exists.elim
        lowerData
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
                        (fun lowerMembership upperAndTriangle =>
                          And.elim
                            upperAndTriangle
                            (fun upperMembership triangle_mem =>
                              Exists.intro
                                lower
                                (Exists.intro
                                  object
                                  (Exists.intro
                                    upper
                                    (Exists.intro
                                      firstMap
                                      (Exists.intro
                                        secondMap
                                        (Exists.intro
                                          connectingMap
                                          (And.intro
                                            rfl
                                            (And.intro
                                              lowerMembership
                                              (And.intro
                                                upperMembership
                                                triangle_mem)))))))))))))))

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
