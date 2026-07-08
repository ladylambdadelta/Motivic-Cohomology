import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Preimage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.AbelianEnvelope.Owner

/-!
# Truncation existence transported from the derived cochain preimage

This file composes the intrinsic abelian-envelope truncation triangle with the
canonical cochain-preimage isomorphism of the derived localization functor.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- Intrinsic short exactness for the canonical cochain preimage gives the
object-level truncation triangle for an arbitrary derived analytic motive. -/
theorem cochainPreimage_exists_truncation_triangle
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  Exists.elim
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsic_exists_truncation_triangle
        cut
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
        hshortExact)
    (fun lower representedResult =>
      Exists.elim representedResult
        (fun upper triangleData =>
          And.elim triangleData
            (fun lowerMembership upperAndTriangle =>
              And.elim upperAndTriangle
                (fun upperMembership triangleExists =>
                  Exists.elim triangleExists
                    (fun firstMap secondAndConnecting =>
                      Exists.elim secondAndConnecting
                        (fun secondMap connectingAndDistinguished =>
                          Exists.elim connectingAndDistinguished
                            (fun connectingMap oldDistinguished =>
                              let preimageIso :
                                  TraceAnalyticDerivedMotiveCategory.objectOf
                                      (TraceAnalyticDerivedMotiveCategory
                                        .cochainPreimage object) ≅
                                    object :=
                                TraceAnalyticDerivedMotiveCategory
                                  .objectOfCochainPreimageIso object
                              let oldTriangle :
                                  Triangle
                                    TraceAnalyticDerivedMotiveCategory :=
                                Triangle.mk
                                  firstMap
                                  secondMap
                                  connectingMap
                              let transportedTriangle :
                                  Triangle
                                    TraceAnalyticDerivedMotiveCategory :=
                                Triangle.mk
                                  (firstMap ≫ preimageIso.hom)
                                  (preimageIso.inv ≫ secondMap)
                                  connectingMap
                              let triangleIso :
                                  oldTriangle ≅ transportedTriangle :=
                                Triangle.isoMk
                                  oldTriangle
                                  transportedTriangle
                                  (Iso.refl lower)
                                  preimageIso
                                  (Iso.refl upper)
                                  (Eq.trans
                                    (Category.comp_id
                                      (firstMap ≫ preimageIso.hom))
                                    (Eq.symm
                                      (Category.id_comp
                                        (firstMap ≫ preimageIso.hom))))
                                  (Eq.trans
                                    (Category.comp_id secondMap)
                                    (Eq.symm
                                      (Eq.trans
                                        (Category.assoc
                                          preimageIso.hom
                                          preimageIso.inv
                                          secondMap)
                                        (Eq.trans
                                          (congrArg
                                            (fun map => map ≫ secondMap)
                                            preimageIso.hom_inv_id)
                                          (Category.id_comp secondMap)))))
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
                                        (firstMap ≫ preimageIso.hom)
                                        (Exists.intro
                                          (preimageIso.inv ≫ secondMap)
                                          (Exists.intro
                                            connectingMap
                                            (isomorphic_distinguished
                                              oldTriangle
                                              oldDistinguished
                                              transportedTriangle
                                              triangleIso)))))))))))))

/-- Normalized intrinsic short exactness for the canonical cochain preimage
gives the adjacent `≤ 0`, `≥ 1` truncation triangle for an arbitrary derived
analytic motive. -/
theorem cochainPreimage_exists_triangle_zero_one
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .cochainPreimage_exists_truncation_triangle
      1
      object
      hshortExact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
