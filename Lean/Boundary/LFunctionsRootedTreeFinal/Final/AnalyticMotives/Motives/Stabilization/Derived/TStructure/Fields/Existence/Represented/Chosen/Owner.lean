import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Owner

/-!
# Chosen truncation data from a Yoneda representative

This file turns concrete Yoneda truncation representative data into named
lower and upper vertices, maps, and the distinguished truncation triangle for
the represented derived object.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives
namespace TraceAnalyticMotivicTStructure

namespace YonedaTruncationRepresentative

/-- The cochain short exactness witness attached to a Yoneda representative. -/
def shortExact
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortComplex
          cut
          representative.complex) :=
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
      cut
      representative.complex
      representative.degreewiseShortExact

/-- The chosen lower truncation vertex attached to a Yoneda representative. -/
def lowerObject
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    TraceAnalyticDerivedMotiveCategory :=
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedLowerVertex
      cut
      representative.complex
      representative.shortExact

/-- The chosen upper truncation vertex attached to a Yoneda representative. -/
def upperObject
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    TraceAnalyticDerivedMotiveCategory :=
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedUpperVertex
      cut
      representative.complex
      representative.shortExact

/-- The chosen first truncation map attached to a Yoneda representative. -/
def firstMap
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.lowerObject ⟶ object :=
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedLowerMap
        cut
        representative.complex
        representative.shortExact ≫
    representative.iso.inv

/-- The chosen second truncation map attached to a Yoneda representative. -/
def secondMap
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    object ⟶ representative.upperObject :=
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  representative.iso.hom ≫
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedUpperMap
        cut
        representative.complex
        representative.shortExact

/-- The chosen connecting map attached to a Yoneda representative. -/
def connectingMap
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.upperObject ⟶ representative.lowerObject⟦(1 : ℤ)⟧ :=
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedConnectingMapFromSubcategories
      cut
      representative.complex
      representative.shortExact

/-- The chosen truncation triangle attached to a Yoneda representative. -/
def triangle
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    Triangle TraceAnalyticDerivedMotiveCategory :=
  Triangle.mk
    representative.firstMap
    representative.secondMap
    representative.connectingMap

/-- The chosen lower vertex has the expected homological upper bound. -/
theorem lowerObject_mem
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
      representative.lowerObject :=
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangle_obj₁_homologicalLE
      cut
      representative.complex
      representative.shortExact

/-- The chosen upper vertex has the expected homological lower bound. -/
theorem upperObject_mem
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE cut
      representative.upperObject :=
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangle_obj₃_homologicalGE
      cut
      representative.complex
      representative.shortExact

/-- The chosen truncation triangle is distinguished. -/
theorem triangle_distinguished
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.triangle ∈
      distTriang TraceAnalyticDerivedMotiveCategory :=
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  let oldTriangle : Triangle TraceAnalyticDerivedMotiveCategory :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle
        cut
        representative.complex
        representative.shortExact
  let triangleIso : representative.triangle ≅ oldTriangle :=
    Triangle.isoMk
      representative.triangle
      oldTriangle
      (Iso.refl representative.lowerObject)
      representative.iso
      (Iso.refl representative.upperObject)
      (Eq.trans
        (Category.assoc
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionDerivedLowerMap
              cut
              representative.complex
              representative.shortExact)
          representative.iso.inv
          representative.iso.hom)
        (Eq.trans
          (congrArg
            (fun map =>
              TraceAnalyticMotivicTStructure
                  .abelianEnvelopeCochainDecompositionDerivedLowerMap
                    cut
                    representative.complex
                    representative.shortExact ≫
                map)
            representative.iso.inv_hom_id)
          (Eq.trans
            (Category.comp_id
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeCochainDecompositionDerivedLowerMap
                  cut
                  representative.complex
                  representative.shortExact))
            (Eq.symm
              (Category.id_comp
                (TraceAnalyticMotivicTStructure
                  .abelianEnvelopeCochainDecompositionDerivedLowerMap
                    cut
                    representative.complex
                    representative.shortExact))))))
      (Category.comp_id
        (representative.iso.hom ≫
          TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionDerivedUpperMap
              cut
              representative.complex
              representative.shortExact))
      (Eq.trans
        (Category.comp_id
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionDerivedConnectingMapFromSubcategories
              cut
              representative.complex
              representative.shortExact))
        (Eq.symm
          (Category.id_comp
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionDerivedConnectingMapFromSubcategories
                cut
                representative.complex
                representative.shortExact))))
  isomorphic_distinguished
    oldTriangle
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle_distinguished
        cut
        representative.complex
        representative.shortExact)
    representative.triangle
    triangleIso.symm

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
