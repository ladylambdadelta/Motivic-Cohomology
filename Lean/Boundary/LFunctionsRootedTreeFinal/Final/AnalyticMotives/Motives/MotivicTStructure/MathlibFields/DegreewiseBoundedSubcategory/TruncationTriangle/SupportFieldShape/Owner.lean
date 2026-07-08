import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportPredicates.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.TruncationTriangle.Representative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.Complexes.GE.Owner

/-!
# Support-shaped truncation field for degreewise bounded objects

This file upgrades the concrete representative truncation triangle to an
arbitrary degreewise bounded stable object, using the representative iso to
transport the middle vertex.  The lower and upper vertices are certified by the
iso-closed support predicates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The normalized lower cut paired with upper cut `1` is `0`. -/
theorem decompositionLowerCut_one :
    TraceAnalyticMotivicTStructure.decompositionLowerCut 1 = 0 :=
  rfl

/-- Source cochain complexes have all homology objects needed by the
truncation calculus. -/
theorem degreewiseCochainRepresentative_hasHomology
    (complex : TraceAnalyticAdditiveCochainComplex) :
    ∀ degree, complex.HasHomology degree :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainComplex_hasHomology_all complex

/-- A representative truncation triangle can be transported across an
isomorphism of its middle vertex while preserving the same lower and upper
support certificates. -/
theorem degreewiseRepresentative_exists_supported_triangle_at_iso_middle
    {representative middle : TraceAnalyticDMgmComparisonSource}
    (middleIso : representative ≅ middle)
    (representativeTriangle :
      ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportedLEIsoClosedAmbient 0 lower ∧
          TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
              .supportedGEIsoClosedAmbient 1 upper ∧
            ∃ (firstMap : lower ⟶ representative)
              (secondMap : representative ⟶ upper)
              (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
              Triangle.mk firstMap secondMap connectingMap ∈
                TraceAnalyticDMgmComparisonSource.distinguishedTriangles) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportedLEIsoClosedAmbient 0 lower ∧
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportedGEIsoClosedAmbient 1 upper ∧
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
                              let transportedTriangle :
                                  Triangle
                                    TraceAnalyticStableMotiveCategory :=
                                Triangle.mk
                                  (firstMap ≫ middleIso.hom)
                                  (middleIso.inv ≫ secondMap)
                                  connectingMap
                              let oldTriangle :
                                  Triangle
                                    TraceAnalyticStableMotiveCategory :=
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
                                            (isomorphic_distinguished
                                              oldTriangle
                                              oldDistinguished
                                              transportedTriangle
                                              triangleIso.symm)))))))))))))))

/-- Concrete representative field shape at upper cut `1`, with lower cut
normalized to `0`. -/
theorem degreewiseRepresentative_exists_supported_triangle_zero_one
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        1
        complex)] :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportedLEIsoClosedAmbient 0 lower ∧
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportedGEIsoClosedAmbient 1 upper ∧
          ∃ (firstMap : lower ⟶
              TraceAnalyticDMgmComparisonSource.objectOf
                (TraceAnalyticAdditiveHomotopyCategory.objectOf complex))
            (secondMap :
              TraceAnalyticDMgmComparisonSource.objectOf
                  (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ⟶
                upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  let triangle :
      Triangle TraceAnalyticStableMotiveCategory :=
    TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle 1 complex
  let lowerMembership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEIsoClosedAmbient 0 triangle.obj₁ :=
    Eq.subst
      (motive := fun cut =>
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportedLEIsoClosedAmbient cut triangle.obj₁)
      TraceAnalyticMotivicTStructure.decompositionLowerCut_one
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEAmbient_le_supportedLEIsoClosedAmbient
          (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)
          (TraceAnalyticMotivicTStructure
            .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₁_supportedLE
              1
              complex
              bounded))
  let upperMembership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEIsoClosedAmbient 1 triangle.obj₃ :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedGEAmbient_le_supportedGEIsoClosedAmbient
        1
        (TraceAnalyticMotivicTStructure
          .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₃_supportedGE
            1
            complex
            bounded)
  Exists.intro
    triangle.obj₁
    (Exists.intro
      triangle.obj₃
      (And.intro
        lowerMembership
        (And.intro
          upperMembership
          (Exists.intro
            triangle.mor₁
            (Exists.intro
              triangle.mor₂
              (Exists.intro
                triangle.mor₃
                (TraceAnalyticMotivicTStructure
                  .stableCochainDecompositionTransportedTriangle_distinguished
                    1
                    complex)))))))

/-- Support-shaped truncation triangle for every degreewise bounded stable
object. -/
theorem degreewiseBoundedObject_exists_supported_triangle_zero_one
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap 1 complex)) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportedLEIsoClosedAmbient 0 lower ∧
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportedGEIsoClosedAmbient 1 upper ∧
          ∃ (firstMap : lower ⟶ object.object)
            (secondMap : object.object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
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
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex) :=
                coneComparison complex bounded
              TraceAnalyticMotivicTStructure
                .degreewiseRepresentative_exists_supported_triangle_at_iso_middle
                  representativeIso
                  (TraceAnalyticMotivicTStructure
                    .degreewiseRepresentative_exists_supported_triangle_zero_one
                      complex
                      bounded))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
