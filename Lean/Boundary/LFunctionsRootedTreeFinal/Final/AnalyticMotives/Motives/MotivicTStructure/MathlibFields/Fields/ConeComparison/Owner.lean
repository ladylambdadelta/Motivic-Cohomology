import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.IsIso.IdentityCone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Fields.Owner

/-!
# Cone-comparison field for Mathlib truncation triangles

This file exposes the concrete identity-cone route from a cochain-level
isomorphism of the normalized cone-to-upper map to the stable cone-comparison
isomorphism used by the Mathlib-facing truncation triangle field.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- A cochain-level isomorphism of every normalized cone-to-upper map supplies
the stable cone-comparison isomorphism family used by the bounded-source
truncation field. -/
theorem tStructure_coneComparison_of_isIso_cochainMap
    (cut : ℤ)
    (cochainComparison :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        IsIso
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              cut
              complex.complex))
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex.complex) :=
  letI :
      IsIso
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
          cut
          complex.complex) :=
    cochainComparison complex
  TraceAnalyticMotivicTStructure
    .stableNormalizedConeComparisonMap_isIso_of_isIso_cochainMap
      cut
      complex.complex

/-- At Mathlib cut `0`, a cochain-level isomorphism family supplies the exact
cone-comparison family required by the bounded-source truncation field. -/
theorem tStructure_cutZero_coneComparison_of_isIso_cochainMap
    (cochainComparison :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        IsIso
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              0
              complex.complex))
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        0
        complex.complex) :=
  TraceAnalyticMotivicTStructure.tStructure_coneComparison_of_isIso_cochainMap
    0
    cochainComparison
    complex

/-- If every named normalized cone-comparison cone object is the middle vertex
of a distinguished extension of stable-null objects, then the bounded-source
truncation field has the required stable cone-comparison isomorphism family. -/
theorem tStructure_coneComparison_of_coneObject_extension
    (cut : ℤ)
    (coneTriangle :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        CategoryTheory.Pretriangulated.Triangle
          TraceAnalyticAdditiveHomotopyCategory)
    (coneDistinguished :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        coneTriangle complex ∈
          TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (coneVertexEq :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonConeObject
              cut
              complex.complex =
          (coneTriangle complex).obj₂)
    (left :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticStableNullSubcategory.P
          (coneTriangle complex).obj₁)
    (right :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticStableNullSubcategory.P
          (coneTriangle complex).obj₃)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex.complex) :=
  TraceAnalyticMotivicTStructure
    .stableNormalizedConeComparisonMap_isIso_of_coneObject_extension
      cut
      complex.complex
      (coneTriangle complex)
      (coneDistinguished complex)
      (coneVertexEq complex)
      (left complex)
      (right complex)

/-- At Mathlib cut `0`, extension-null cone presentations supply the exact
cone-comparison family required by the bounded-source truncation field. -/
theorem tStructure_cutZero_coneComparison_of_coneObject_extension
    (coneTriangle :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        CategoryTheory.Pretriangulated.Triangle
          TraceAnalyticAdditiveHomotopyCategory)
    (coneDistinguished :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        coneTriangle complex ∈
          TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (coneVertexEq :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonConeObject
              0
              complex.complex =
          (coneTriangle complex).obj₂)
    (left :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticStableNullSubcategory.P
          (coneTriangle complex).obj₁)
    (right :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticStableNullSubcategory.P
          (coneTriangle complex).obj₃)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        0
        complex.complex) :=
  TraceAnalyticMotivicTStructure
    .tStructure_coneComparison_of_coneObject_extension
      0
      coneTriangle
      coneDistinguished
      coneVertexEq
      left
      right
      complex

/-- The bounded-source truncation field can be invoked using the cochain-level
cone-comparison isomorphism family which the identity-cone calculus reduces to
stable cone-comparison isomorphisms. -/
theorem tStructure_exists_triangle_zero_one_of_boundedStableObject_of_isIso_cochainMap
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (cochainComparison :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        IsIso
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              0
              complex.complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.tStructureLE 0 lower ∧
        TraceAnalyticMotivicTStructure.tStructureGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            CategoryTheory.Pretriangulated.Triangle.mk
                firstMap
                secondMap
                connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .tStructure_exists_triangle_zero_one_of_boundedStableObject
      membership
      homology
      cochainComparison

/-- The bounded-source truncation field can be invoked using the cochain-level
cone-comparison isomorphism family, in the exact field order used by
`TStructure.exists_triangle_zero_one`. -/
theorem tStructure_exists_triangle_zero_one_of_boundedStableObject_of_isIso_cochainMap_fieldShape
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (cochainComparison :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        IsIso
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              0
              complex.complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ : TraceAnalyticMotivicTStructure.tStructureLE 0 lower)
      (_ : TraceAnalyticMotivicTStructure.tStructureGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      CategoryTheory.Pretriangulated.Triangle.mk
          firstMap
          secondMap
          connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .tStructure_exists_triangle_zero_one_of_boundedStableObject_fieldShape
      membership
      homology
      cochainComparison

/-- The bounded-source truncation field can be invoked using the concrete
Verdier extension criterion for the named normalized cone-comparison cone
objects. -/
theorem tStructure_exists_triangle_zero_one_of_boundedStableObject_of_coneObject_extension
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (coneTriangle :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        CategoryTheory.Pretriangulated.Triangle
          TraceAnalyticAdditiveHomotopyCategory)
    (coneDistinguished :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        coneTriangle complex ∈
          TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (coneVertexEq :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonConeObject
              0
              complex.complex =
          (coneTriangle complex).obj₂)
    (left :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticStableNullSubcategory.P
          (coneTriangle complex).obj₁)
    (right :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticStableNullSubcategory.P
          (coneTriangle complex).obj₃) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.tStructureLE 0 lower ∧
        TraceAnalyticMotivicTStructure.tStructureGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            CategoryTheory.Pretriangulated.Triangle.mk
                firstMap
                secondMap
                connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .tStructure_exists_triangle_zero_one_of_boundedStableObject
      membership
      homology
      (fun complex =>
        TraceAnalyticMotivicTStructure
          .tStructure_cutZero_coneComparison_of_coneObject_extension
            coneTriangle
            coneDistinguished
            coneVertexEq
            left
            right
            complex)

/-- The bounded-source truncation field can be invoked using the concrete
Verdier extension criterion for the named normalized cone-comparison cone
objects, in the exact field order used by
`TStructure.exists_triangle_zero_one`. -/
theorem tStructure_exists_triangle_zero_one_of_boundedStableObject_of_coneObject_extension_fieldShape
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (coneTriangle :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        CategoryTheory.Pretriangulated.Triangle
          TraceAnalyticAdditiveHomotopyCategory)
    (coneDistinguished :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        coneTriangle complex ∈
          TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (coneVertexEq :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonConeObject
              0
              complex.complex =
          (coneTriangle complex).obj₂)
    (left :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticStableNullSubcategory.P
          (coneTriangle complex).obj₁)
    (right :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        TraceAnalyticStableNullSubcategory.P
          (coneTriangle complex).obj₃) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ : TraceAnalyticMotivicTStructure.tStructureLE 0 lower)
      (_ : TraceAnalyticMotivicTStructure.tStructureGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      CategoryTheory.Pretriangulated.Triangle.mk
          firstMap
          secondMap
          connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  TraceAnalyticMotivicTStructure
    .tStructure_exists_triangle_zero_one_of_boundedStableObject_fieldShape
      membership
      homology
      (fun complex =>
        TraceAnalyticMotivicTStructure
          .tStructure_cutZero_coneComparison_of_coneObject_extension
            coneTriangle
            coneDistinguished
            coneVertexEq
            left
            right
            complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
