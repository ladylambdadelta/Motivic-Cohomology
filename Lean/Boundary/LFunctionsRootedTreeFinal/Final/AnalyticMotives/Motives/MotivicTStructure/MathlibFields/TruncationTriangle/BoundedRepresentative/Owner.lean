import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Stable.Bounds.Membership.Reindexed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.ShortComplex.Certificate.Projections.Owner

/-!
# Mathlib-shaped truncation triangles for bounded representatives

This file assembles the concrete stable cochain-decomposition triangle with
the Mathlib-facing membership facts for its lower and upper truncation vertices.
It is the representative-level `exists_triangle_zero_one` input for the
bounded analytic source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The lower vertex of the transported cochain-decomposition triangle is the
stable lower truncation at the paired lower cut. -/
theorem stableCochainDecompositionTransportedTriangle_obj₁
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex.complex).obj₁ =
      TraceAnalyticMotivicTStructure.stableTruncLE
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
        complex.complex :=
  TraceAnalyticMotivicTStructure
    .stableCochainDecompositionTransportedTriangle_raw_obj₁ cut complex.complex

/-- The middle vertex of the transported cochain-decomposition triangle is the
stable image of the original bounded cochain complex. -/
theorem stableCochainDecompositionTransportedTriangle_obj₂
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex.complex).obj₂ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex.complex) :=
  TraceAnalyticMotivicTStructure
    .stableCochainDecompositionTransportedTriangle_raw_obj₂ cut complex.complex

/-- The upper vertex of the transported cochain-decomposition triangle is the
stable upper truncation at the chosen upper cut. -/
theorem stableCochainDecompositionTransportedTriangle_obj₃
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex.complex).obj₃ =
      TraceAnalyticMotivicTStructure.stableTruncGE cut complex.complex :=
  TraceAnalyticMotivicTStructure
    .stableCochainDecompositionTransportedTriangle_raw_obj₃ cut complex.complex

/-- The first morphism of the transported cochain-decomposition triangle is
the stable lower truncation inclusion. -/
theorem stableCochainDecompositionTransportedTriangle_firstMap
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex.complex).mor₁ =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex.complex).f :=
  TraceAnalyticMotivicTStructure
    .stableCochainDecompositionTransportedTriangle_raw_firstMap cut complex.complex

/-- The second morphism of the transported cochain-decomposition triangle is
the stable upper truncation projection. -/
theorem stableCochainDecompositionTransportedTriangle_secondMap
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex.complex).mor₂ =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex.complex).g :=
  TraceAnalyticMotivicTStructure
    .stableCochainDecompositionTransportedTriangle_raw_secondMap cut complex.complex

/-- The third morphism of the transported cochain-decomposition triangle is the
transported connecting map. -/
theorem stableCochainDecompositionTransportedTriangle_thirdMap
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedTriangle
      cut
      complex.complex).mor₃ =
      TraceAnalyticMotivicTStructure.stableCochainDecompositionTransportedConnectingMap
        cut
        complex.complex :=
  TraceAnalyticMotivicTStructure
    .stableCochainDecompositionTransportedTriangle_raw_thirdMap cut complex.complex

/-- The lower vertex of the transported cochain-decomposition triangle lies in
the Mathlib-facing `LE 0` predicate. -/
theorem stableCochainDecompositionTransportedTriangle_obj₁_mem_mathlibLE_zero
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    TraceAnalyticMotivicTStructure.mathlibLE
      0
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex.complex).obj₁ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticMotivicTStructure.mathlibLE 0 object)
    (Eq.symm
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_obj₁ cut complex))
    (TraceAnalyticMotivicTStructure.stableTruncLE_mem_mathlibLE_zero
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
      complex)

/-- The upper vertex of the transported cochain-decomposition triangle lies in
the Mathlib-facing `GE 1` predicate. -/
theorem stableCochainDecompositionTransportedTriangle_obj₃_mem_mathlibGE_one
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    TraceAnalyticMotivicTStructure.mathlibGE
      1
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex.complex).obj₃ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticMotivicTStructure.mathlibGE 1 object)
    (Eq.symm
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_obj₃ cut complex))
    (TraceAnalyticMotivicTStructure.stableTruncGE_mem_mathlibGE_one
      cut
      complex)

/-- Representative-level Mathlib-shaped truncation triangle for a bounded
analytic cochain complex. -/
theorem boundedRepresentative_exists_triangle_zero_one_objectOf
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
        TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
          ∃ (firstMap :
              lower ⟶
                TraceAnalyticDMgmComparisonSource.objectOf
                  (TraceAnalyticAdditiveHomotopyCategory.objectOf
                    complex.complex))
            (secondMap :
              TraceAnalyticDMgmComparisonSource.objectOf
                  (TraceAnalyticAdditiveHomotopyCategory.objectOf
                    complex.complex) ⟶
                upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  let triangle :
      Triangle TraceAnalyticStableMotiveCategory :=
    TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle cut complex.complex
  Exists.intro
    triangle.obj₁
    (Exists.intro
      triangle.obj₃
      (And.intro
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle_obj₁_mem_mathlibLE_zero
            cut
            complex)
        (And.intro
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle_obj₃_mem_mathlibGE_one
              cut
              complex)
          (Exists.intro
            triangle.mor₁
            (Exists.intro
              triangle.mor₂
              (Exists.intro
                triangle.mor₃
                (TraceAnalyticMotivicTStructure
                  .stableCochainDecompositionTransportedTriangle_distinguished
                    cut
                    complex.complex)))))))

/-- Concrete bounded-representative truncation-triangle certificate before
forgetting the chosen transported triangle to the Mathlib existential field.

This keeps the analytic cone map visible at the field-owner level: the third
map is the transported connecting morphism produced by the normalized
cochain-decomposition cone comparison. -/
theorem boundedRepresentative_concrete_truncation_triangle_certificate
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    TraceAnalyticMotivicTStructure.mathlibLE
        0
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle
            cut
            complex.complex).obj₁ ∧
      TraceAnalyticMotivicTStructure.mathlibGE
          1
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle
              cut
              complex.complex).obj₃ ∧
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle
            cut
            complex.complex).obj₂ =
          TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticAdditiveHomotopyCategory.objectOf
              complex.complex) ∧
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle
              cut
              complex.complex).mor₁ =
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionShortComplex
                cut
                complex.complex).f ∧
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionTransportedTriangle
                cut
                complex.complex).mor₂ =
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionShortComplex
                  cut
                  complex.complex).g ∧
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionTransportedTriangle
                  cut
                  complex.complex).mor₃ =
                TraceAnalyticMotivicTStructure
                  .stableCochainDecompositionTransportedConnectingMap
                    cut
                    complex.complex ∧
                TraceAnalyticMotivicTStructure
                  .stableCochainDecompositionTransportedTriangle
                    cut
                    complex.complex ∈
                  TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  And.intro
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle_obj₁_mem_mathlibLE_zero
        cut
        complex)
    (And.intro
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_obj₃_mem_mathlibGE_one
          cut
          complex)
      (And.intro
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle_obj₂ cut complex)
        (And.intro
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle_firstMap
              cut
              complex)
          (And.intro
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionTransportedTriangle_secondMap
                cut
                complex)
            (And.intro
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionTransportedTriangle_thirdMap
                  cut
                  complex)
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionTransportedTriangle_distinguished
                  cut
                  complex.complex))))))

/-- Representative-level Mathlib-shaped truncation triangle for a bounded
analytic cochain complex in the exact field order used by
`TStructure.exists_triangle_zero_one`. -/
theorem boundedRepresentative_exists_triangle_zero_one_objectOf_fieldShape
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ : TraceAnalyticMotivicTStructure.mathlibLE 0 lower)
      (_ : TraceAnalyticMotivicTStructure.mathlibGE 1 upper)
      (firstMap :
        lower ⟶
          TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticAdditiveHomotopyCategory.objectOf
              complex.complex))
      (secondMap :
        TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticAdditiveHomotopyCategory.objectOf
              complex.complex) ⟶
          upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  Exists.elim
    (TraceAnalyticMotivicTStructure
      .boundedRepresentative_exists_triangle_zero_one_objectOf cut complex)
    (fun lower lowerData =>
      Exists.elim
        lowerData
        (fun upper upperData =>
          And.elim
            upperData
            (fun lowerMembership upperAndTriangle =>
              And.elim
                upperAndTriangle
                (fun upperMembership triangleData =>
                  Exists.elim
                    triangleData
                    (fun firstMap firstMapData =>
                      Exists.elim
                        firstMapData
                        (fun secondMap secondMapData =>
                          Exists.elim
                            secondMapData
                            (fun connectingMap distinguished =>
                              Exists.intro
                                lower
                                (Exists.intro
                                  upper
                                  (Exists.intro
                                    lowerMembership
                                    (Exists.intro
                                      upperMembership
                                      (Exists.intro
                                        firstMap
                                        (Exists.intro
                                          secondMap
                                          (Exists.intro
                                            connectingMap
                                            distinguished)))))))))))))

/-- The representative truncation triangle is backed by the named stable
cochain-decomposition short complex, with zero composition and paired
preadditive Yoneda exactness. -/
theorem boundedRepresentative_stableCochainDecompositionShortComplex_certificate
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)]
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex.complex).X₁ =
        TraceAnalyticDMgmComparisonSource.objectOf
          (TraceAnalyticAdditiveHomotopyCategory.objectOf
            (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
              cut
              complex.complex)) ∧
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex.complex).X₂ =
        TraceAnalyticDMgmComparisonSource.objectOf
          (TraceAnalyticAdditiveHomotopyCategory.objectOf
            complex.complex) ∧
        (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
          cut
          complex.complex).X₃ =
          TraceAnalyticMotivicTStructure.stableTruncGE cut complex.complex ∧
          (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
            cut
            complex.complex).f =
            TraceAnalyticDMgmComparisonSource.mapOf
              (TraceAnalyticAdditiveHomotopyCategory.mapOf
                (TraceAnalyticMotivicTStructure
                  .additiveCochainDecompositionLowerMap cut complex.complex)) ∧
            (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
              cut
              complex.complex).g =
              TraceAnalyticMotivicTStructure.stableTruncGEProjectionMap
                cut
                complex.complex ∧
              (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
                cut
                complex.complex).f ≫
                  (TraceAnalyticMotivicTStructure
                    .stableCochainDecompositionShortComplex
                      cut
                      complex.complex).g =
                0 ∧
                ((TraceAnalyticMotivicTStructure
                  .stableCochainDecompositionShortComplex
                    cut
                    complex.complex).map
                    (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                  ((TraceAnalyticMotivicTStructure
                    .stableCochainDecompositionShortComplex
                      cut
                      complex.complex).op.map
                      (preadditiveYoneda.obj rightProbe)).Exact :=
  TraceAnalyticMotivicTStructure
    .stableCochainDecompositionShortComplex_certificate_of_isIso_cochainMap
      cut
      complex.complex
      leftProbe
      rightProbe

/-- Representative-level Mathlib-shaped truncation triangle with the middle
vertex written as the comparison-facing stable bounded object. -/
theorem boundedRepresentative_exists_triangle_zero_one_sourceStableWeightBoundedObject
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex.complex)] :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
        TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
          ∃ (firstMap :
              lower ⟶
                TraceAnalyticMotiveComparison
                  .sourceStableWeightBoundedObject complex)
            (secondMap :
              TraceAnalyticMotiveComparison
                  .sourceStableWeightBoundedObject complex ⟶
                upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  let middle_eq :
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          complex =
        TraceAnalyticDMgmComparisonSource.objectOf
          (TraceAnalyticAdditiveHomotopyCategory.objectOf
            complex.complex) :=
    Eq.trans
      (TraceAnalyticMotiveComparison
        .sourceStableWeightBoundedObject_eq complex)
      (congrArg
        TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticMotiveComparison
          .sourceWeightBoundedHomotopyObject_eq complex))
  Eq.subst
    (motive := fun middle =>
      ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
        TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
          TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
            ∃ (firstMap : lower ⟶ middle)
              (secondMap : middle ⟶ upper)
              (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
              Triangle.mk firstMap secondMap connectingMap ∈
                TraceAnalyticDMgmComparisonSource.distinguishedTriangles)
    (Eq.symm middle_eq)
    (TraceAnalyticMotivicTStructure
      .boundedRepresentative_exists_triangle_zero_one_objectOf cut complex)

/-- Pull a representative truncation triangle back along an isomorphism of its
middle vertex. -/
theorem boundedRepresentative_exists_triangle_zero_one_of_middleIso
    {middle representative : TraceAnalyticDMgmComparisonSource}
    (middleIso : middle ≅ representative)
    (representativeTriangle :
      ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
        TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
          TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
            ∃ (firstMap : lower ⟶ representative)
              (secondMap : representative ⟶ upper)
              (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
              Triangle.mk firstMap secondMap connectingMap ∈
                TraceAnalyticDMgmComparisonSource.distinguishedTriangles) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
        TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
          ∃ (firstMap : lower ⟶ middle)
            (secondMap : middle ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  Exists.elim
    representativeTriangle
    (fun lower lowerData =>
      Exists.elim
        lowerData
        (fun upper upperData =>
          And.elim
            upperData
            (fun lowerMembership upperAndTriangle =>
              And.elim
                upperAndTriangle
                (fun upperMembership triangleData =>
                  Exists.elim
                    triangleData
                    (fun firstMap firstMapData =>
                      Exists.elim
                        firstMapData
                        (fun secondMap secondMapData =>
                          Exists.elim
                            secondMapData
                            (fun connectingMap oldDistinguished =>
                              let pulledTriangle :
                                  Triangle
                                    TraceAnalyticStableMotiveCategory :=
                                Triangle.mk
                                  (firstMap ≫ middleIso.inv)
                                  (middleIso.hom ≫ secondMap)
                                  connectingMap
                              let oldTriangle :
                                  Triangle
                                    TraceAnalyticStableMotiveCategory :=
                                Triangle.mk
                                  firstMap
                                  secondMap
                                  connectingMap
                              let triangleIso :
                                  pulledTriangle ≅ oldTriangle :=
                                Triangle.isoMk
                                  pulledTriangle
                                  oldTriangle
                                  (Iso.refl lower)
                                  middleIso
                                  (Iso.refl upper)
                                  (Eq.trans
                                    (Category.assoc
                                      firstMap
                                      middleIso.inv
                                      middleIso.hom)
                                    (Eq.trans
                                      (congrArg
                                        (fun map => firstMap ≫ map)
                                        middleIso.inv_hom_id)
                                      (Eq.trans
                                        (Category.comp_id firstMap)
                                        (Eq.symm
                                          (Category.id_comp firstMap)))))
                                  (Category.comp_id
                                    (middleIso.hom ≫ secondMap))
                                  (Eq.trans
                                    (Category.comp_id connectingMap)
                                    (Eq.symm
                                      (Category.id_comp connectingMap)))
                              Exists.intro
                                lower
                                (Exists.intro
                                  upper
                                  (And.intro
                                    lowerMembership
                                    (And.intro
                                      upperMembership
                                      (Exists.intro
                                        (firstMap ≫ middleIso.inv)
                                        (Exists.intro
                                          (middleIso.hom ≫ secondMap)
                                          (Exists.intro
                                            connectingMap
                                            (isomorphic_distinguished
                                              oldTriangle
                                              oldDistinguished
                                              pulledTriangle
                                              triangleIso.symm)))))))))))))))

/-- Mathlib-shaped truncation triangle for every bounded stable object which is
iso-represented by a bounded analytic cochain complex. -/
theorem boundedStableObject_exists_triangle_zero_one
    (cut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (coneComparison :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        IsIso
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              cut
              complex.complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticMotivicTStructure.mathlibLE 0 lower ∧
        TraceAnalyticMotivicTStructure.mathlibGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  Exists.elim
    membership
    (fun representative representativeData =>
      Exists.elim
        representativeData
        (fun representativeMembership representativeIso =>
          Nonempty.elim
            representativeIso
            (fun middleIso =>
              Exists.elim
                representativeMembership
                (fun bound boundData =>
                  Exists.elim
                    boundData
                    (fun complex representative_eq =>
                      letI :
                          ∀ degree, complex.complex.HasHomology degree :=
                        homology complex
                      letI :
                          IsIso
                            (TraceAnalyticMotivicTStructure
                              .additiveNormalizedConeComparisonCochainMap
                                cut
                                complex.complex) :=
                        coneComparison complex
                      let sourceTriangle :
                          ∃ (lower upper :
                              TraceAnalyticDMgmComparisonSource),
                            TraceAnalyticMotivicTStructure.mathlibLE
                                0 lower ∧
                              TraceAnalyticMotivicTStructure.mathlibGE
                                  1 upper ∧
                                ∃ (firstMap : lower ⟶
                                    TraceAnalyticMotiveComparison
                                      .sourceStableWeightBoundedObject
                                        complex)
                                  (secondMap :
                                    TraceAnalyticMotiveComparison
                                        .sourceStableWeightBoundedObject
                                          complex ⟶ upper)
                                  (connectingMap :
                                    upper ⟶ lower⟦(1 : ℤ)⟧),
                                  Triangle.mk
                                      firstMap
                                      secondMap
                                      connectingMap ∈
                                    TraceAnalyticDMgmComparisonSource
                                      .distinguishedTriangles :=
                        (TraceAnalyticMotivicTStructure
                          .boundedRepresentative_exists_triangle_zero_one_sourceStableWeightBoundedObject
                            cut
                            complex)
                      let representativeTriangle :
                          ∃ (lower upper :
                              TraceAnalyticDMgmComparisonSource),
                            TraceAnalyticMotivicTStructure.mathlibLE
                                0 lower ∧
                              TraceAnalyticMotivicTStructure.mathlibGE
                                  1 upper ∧
                                ∃ (firstMap : lower ⟶ representative)
                                  (secondMap : representative ⟶ upper)
                                  (connectingMap :
                                    upper ⟶ lower⟦(1 : ℤ)⟧),
                                  Triangle.mk
                                      firstMap
                                      secondMap
                                      connectingMap ∈
                                    TraceAnalyticDMgmComparisonSource
                                      .distinguishedTriangles :=
                        Eq.subst
                          (motive := fun candidate =>
                            ∃ (lower upper :
                                TraceAnalyticDMgmComparisonSource),
                              TraceAnalyticMotivicTStructure.mathlibLE
                                  0 lower ∧
                                TraceAnalyticMotivicTStructure.mathlibGE
                                    1 upper ∧
                                  ∃ (firstMap : lower ⟶ candidate)
                                    (secondMap : candidate ⟶ upper)
                                    (connectingMap :
                                      upper ⟶ lower⟦(1 : ℤ)⟧),
                                    Triangle.mk
                                        firstMap
                                        secondMap
                                        connectingMap ∈
                                      TraceAnalyticDMgmComparisonSource
                                        .distinguishedTriangles)
                          (Eq.symm representative_eq)
                          sourceTriangle
                      TraceAnalyticMotivicTStructure
                        .boundedRepresentative_exists_triangle_zero_one_of_middleIso
                          middleIso
                          representativeTriangle)))))))

/-- Mathlib-shaped truncation triangle for every bounded stable object in the
exact field order used by `TStructure.exists_triangle_zero_one`. -/
theorem boundedStableObject_exists_triangle_zero_one_fieldShape
    (cut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object)
    (homology :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        ∀ degree, complex.complex.HasHomology degree)
    (coneComparison :
      ∀ {bound : Nat}
        (complex :
          TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
        IsIso
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              cut
              complex.complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (_ : TraceAnalyticMotivicTStructure.mathlibLE 0 lower)
      (_ : TraceAnalyticMotivicTStructure.mathlibGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  Exists.elim
    (TraceAnalyticMotivicTStructure
      .boundedStableObject_exists_triangle_zero_one
        cut
        membership
        homology
        coneComparison)
    (fun lower lowerData =>
      Exists.elim
        lowerData
        (fun upper upperData =>
          And.elim
            upperData
            (fun lowerMembership upperAndTriangle =>
              And.elim
                upperAndTriangle
                (fun upperMembership triangleData =>
                  Exists.elim
                    triangleData
                    (fun firstMap firstMapData =>
                      Exists.elim
                        firstMapData
                        (fun secondMap secondMapData =>
                          Exists.elim
                            secondMapData
                            (fun connectingMap distinguished =>
                              Exists.intro
                                lower
                                (Exists.intro
                                  upper
                                  (Exists.intro
                                    lowerMembership
                                    (Exists.intro
                                      upperMembership
                                      (Exists.intro
                                        firstMap
                                        (Exists.intro
                                          secondMap
                                          (Exists.intro
                                            connectingMap
                                            distinguished)))))))))))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
