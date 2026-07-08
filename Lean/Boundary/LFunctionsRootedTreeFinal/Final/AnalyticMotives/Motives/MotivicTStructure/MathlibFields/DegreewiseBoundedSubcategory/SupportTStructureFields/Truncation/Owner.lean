import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.DistinguishedTriangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Truncation.StableConeComparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.TruncationTriangle.SupportFieldShape.Owner

/-!
# Support-based truncation field in the degreewise bounded source

This file repackages the ambient support-shaped truncation triangle inside the
degreewise bounded stable full subcategory.  The vertices are the concrete
stable lower and upper truncations of a cochain representative, equipped with
their already-proved degreewise-bounded certificates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A concrete degreewise bounded cochain representative as an object of the
degreewise bounded stable source. -/
def cochainRepresentativeObject
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable where
  obj :=
    TraceAnalyticDMgmComparisonSource.objectOf
      (TraceAnalyticAdditiveHomotopyCategory.objectOf complex)
  property :=
    CategoryTheory.le_isoClosure
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableRepresentative
      (TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex))
      (Exists.intro
        bound
        (Exists.intro
          complex
          (And.intro bounded rfl)))

/-- An ambient isomorphism from a cochain representative to a degreewise
bounded object is an isomorphism in the full subcategory. -/
def cochainRepresentativeObjectIso
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (representativeIso :
      TraceAnalyticDMgmComparisonSource.objectOf
          (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ≅
        object.object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .cochainRepresentativeObject complex bounded ≅
      object where
  hom := representativeIso.hom
  inv := representativeIso.inv
  hom_inv_id := representativeIso.hom_inv_id
  inv_hom_id := representativeIso.inv_hom_id

/-- The representative truncation lower vertex as a degreewise bounded stable
object. -/
def representativeSupportTruncationLowerObject
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        1
        complex)] :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable where
  obj :=
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangleOfStableConeComparison
        1
        complex).obj₁
  property :=
    TraceAnalyticMotivicTStructure
      .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₁_bounded
        1
        complex
        bounded

/-- The representative truncation upper vertex as a degreewise bounded stable
object. -/
def representativeSupportTruncationUpperObject
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        1
        complex)] :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable where
  obj :=
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangleOfStableConeComparison
        1
        complex).obj₃
  property :=
    TraceAnalyticMotivicTStructure
      .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₃_bounded
        1
        complex
        bounded

/-- The representative lower vertex satisfies support `LE 0`. -/
theorem representativeSupportTruncationLower_mem_supportTStructureLE_zero
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        1
        complex)] :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE
        0
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .representativeSupportTruncationLowerObject complex bounded) :=
  Eq.subst
    (motive := fun cut =>
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEIsoClosedAmbient
          cut
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangleOfStableConeComparison
              1
              complex).obj₁)
    TraceAnalyticMotivicTStructure.decompositionLowerCut_one
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedLEAmbient_le_supportedLEIsoClosedAmbient
        (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)
        (TraceAnalyticMotivicTStructure
          .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₁_supportedLE
            1
            complex
            bounded))

/-- The representative upper vertex satisfies support `GE 1`. -/
theorem representativeSupportTruncationUpper_mem_supportTStructureGE_one
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        1
        complex)] :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE
        1
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .representativeSupportTruncationUpperObject complex bounded) :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportedGEAmbient_le_supportedGEIsoClosedAmbient
      1
      (TraceAnalyticMotivicTStructure
        .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₃_supportedGE
          1
          complex
          bounded)

/-- Support-shaped truncation triangle for a concrete cochain representative,
now internal to the degreewise bounded stable source. -/
theorem representative_exists_support_truncation_triangle_zero_one
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        1
        complex)] :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureLE 0 lower ∧
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportTStructureGE 1 upper ∧
          ∃ (firstMap : lower ⟶
              TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                .cochainRepresentativeObject complex bounded)
            (secondMap :
              TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                .cochainRepresentativeObject complex bounded ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                .distinguishedTriangles :=
  let middle :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cochainRepresentativeObject complex bounded
  let lower :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .representativeSupportTruncationLowerObject complex bounded
  let upper :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .representativeSupportTruncationUpperObject complex bounded
  let triangle :
      Triangle TraceAnalyticStableMotiveCategory :=
    TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangleOfStableConeComparison
        1
        complex
  Exists.intro
    lower
    (Exists.intro
      upper
      (And.intro
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .representativeSupportTruncationLower_mem_supportTStructureLE_zero
            complex
            bounded)
        (And.intro
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .representativeSupportTruncationUpper_mem_supportTStructureGE_one
              complex
              bounded)
          (Exists.intro
            triangle.mor₁
            (Exists.intro
              triangle.mor₂
              (Exists.intro
                triangle.mor₃
                (TraceAnalyticMotivicTStructure
                  .stableCochainDecompositionTransportedTriangleOfStableConeComparison_distinguished
                    1
                    complex)))))))

/-- Transport a support truncation triangle across an isomorphism of its middle
vertex inside the degreewise bounded stable source. -/
theorem exists_support_truncation_triangle_at_iso_middle
    {representative middle :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (middleIso : representative ≅ middle)
    (representativeTriangle :
      ∃ (lower upper : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportTStructureLE 0 lower ∧
          TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
              .supportTStructureGE 1 upper ∧
            ∃ (firstMap : lower ⟶ representative)
              (secondMap : representative ⟶ upper)
              (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
              Triangle.mk firstMap secondMap connectingMap ∈
                TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                  .distinguishedTriangles) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureLE 0 lower ∧
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportTStructureGE 1 upper ∧
          ∃ (firstMap : lower ⟶ middle)
            (secondMap : middle ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                .distinguishedTriangles :=
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
                              let transportedTriangle :
                                  Triangle
                                    TraceAnalyticDMgmComparisonSource
                                      .DegreewiseBoundedStable :=
                                Triangle.mk
                                  (firstMap ≫ middleIso.hom)
                                  (middleIso.inv ≫ secondMap)
                                  connectingMap
                              let oldTriangle :
                                  Triangle
                                    TraceAnalyticDMgmComparisonSource
                                      .DegreewiseBoundedStable :=
                                Triangle.mk
                                  firstMap
                                  secondMap
                                  connectingMap
                              let triangleIso :
                                  transportedTriangle ≅ oldTriangle :=
                                Triangle.isoMk
                                  transportedTriangle
                                  oldTriangle
                                  (Iso.refl lower)
                                  middleIso.symm
                                  (Iso.refl upper)
                                  (Eq.trans
                                    (Category.assoc
                                      firstMap
                                      middleIso.hom
                                      middleIso.inv)
                                    (Eq.trans
                                      (congrArg
                                        (fun map => firstMap ≫ map)
                                        middleIso.hom_inv_id)
                                      (Eq.trans
                                        (Category.comp_id firstMap)
                                        (Eq.symm
                                          (Category.id_comp firstMap)))))
                                  (Category.comp_id
                                    (middleIso.inv ≫ secondMap))
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
                                        (firstMap ≫ middleIso.hom)
                                        (Exists.intro
                                          (middleIso.inv ≫ secondMap)
                                          (Exists.intro
                                            connectingMap
                                            (TraceAnalyticDMgmComparisonSource
                                              .DegreewiseBoundedStable
                                              .distinguishedTriangles_isomorphic
                                                oldDistinguished
                                                triangleIso.symm)))))))))))))))

/-- Support-shaped zero-one truncation triangle for every degreewise bounded
stable object. -/
theorem exists_support_truncation_triangle_zero_one
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureLE 0 lower ∧
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportTStructureGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                .distinguishedTriangles :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_degreewiseIsoClosureBoundedCochainRepresentative object)
    (fun bound representativeData =>
      Exists.elim
        representativeData
        (fun complex complexData =>
          And.elim
            complexData
            (fun bounded representativeIso =>
              letI : ∀ degree, complex.HasHomology degree :=
                TraceAnalyticMotivicTStructure
                  .degreewiseCochainRepresentative_hasHomology complex
              letI :
                  IsIso
                    (TraceAnalyticMotivicTStructure
                      .stableNormalizedConeComparisonMap
                        1
                        complex) :=
                coneComparison complex bounded
              TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                .exists_support_truncation_triangle_at_iso_middle
                  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                    .cochainRepresentativeObjectIso
                      complex
                      bounded
                      object
                      representativeIso)
                  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                    .representative_exists_support_truncation_triangle_zero_one
                      complex
                      bounded))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
