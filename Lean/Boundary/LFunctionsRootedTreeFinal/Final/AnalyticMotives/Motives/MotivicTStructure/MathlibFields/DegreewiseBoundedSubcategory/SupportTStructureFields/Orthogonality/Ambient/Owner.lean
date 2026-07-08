import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Orthogonality.Fraction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Orthogonality.IsoClosed.Owner

/-!
# Ambient support orthogonality

This file proves the concrete ambient lower-to-upper orthogonality theorem for
arbitrary stable comparison-source morphisms.  The proof uses the Verdier
left-fraction representation theorem and the homotopy-level support vanishing
already proved for the fraction numerator.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Ambient version of the elementary conjugation cancellation lemma: if a
morphism becomes zero after conjugating by source and target isomorphisms, then
the original morphism is zero. -/
theorem ambient_hom_eq_zero_of_iso_conjugate_eq_zero
    {source target sourceRepresentative targetRepresentative :
      TraceAnalyticDMgmComparisonSource}
    (sourceIso : source ≅ sourceRepresentative)
    (targetIso : target ≅ targetRepresentative)
    (hom : source ⟶ target)
    (conjugate_zero :
      sourceIso.inv ≫ hom ≫ targetIso.hom =
        (0 : sourceRepresentative ⟶ targetRepresentative)) :
    hom = 0 :=
  let source_left_cancel :
      sourceIso.hom ≫ (sourceIso.inv ≫ hom ≫ targetIso.hom) =
        sourceIso.hom ≫
          (0 : sourceRepresentative ⟶ targetRepresentative) :=
    congrArg
      (fun map => sourceIso.hom ≫ map)
      conjugate_zero
  let source_cancelled :
      hom ≫ targetIso.hom =
        sourceIso.hom ≫
          (0 : sourceRepresentative ⟶ targetRepresentative) :=
    Eq.trans
      (Eq.symm
        (Eq.trans
          (Eq.symm
            (Category.assoc sourceIso.hom sourceIso.inv
              (hom ≫ targetIso.hom)))
          (Eq.trans
            (congrArg
              (fun map => map ≫ (hom ≫ targetIso.hom))
              sourceIso.hom_inv_id)
            (Category.id_comp (hom ≫ targetIso.hom)))))
      source_left_cancel
  let source_cancelled_zero :
      hom ≫ targetIso.hom =
        (0 : source ⟶ targetRepresentative) :=
    Eq.trans
      source_cancelled
      (Category.comp_zero sourceIso.hom)
  let target_right_cancel :
      (hom ≫ targetIso.hom) ≫ targetIso.inv =
        (0 : source ⟶ targetRepresentative) ≫ targetIso.inv :=
    congrArg
      (fun map => map ≫ targetIso.inv)
      source_cancelled_zero
  Eq.trans
    (Eq.symm
      (Eq.trans
        (Category.assoc hom targetIso.hom targetIso.inv)
        (Eq.trans
          (congrArg
            (fun map => hom ≫ map)
            targetIso.hom_inv_id)
          (Category.comp_id hom))))
    (Eq.trans
      target_right_cancel
      (Category.zero_comp targetIso.inv))

/-- Concrete ambient support orthogonality for arbitrary stable morphisms:
any morphism from a lower-supported representative at `0` to an upper-supported
representative at `1` is zero in the comparison source. -/
theorem supportedAmbient_zero
    {source target : TraceAnalyticDMgmComparisonSource}
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEAmbient 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEAmbient 1 target)
    (hom : source ⟶ target) :
    hom = 0 :=
  Exists.elim
    source_mem
    (fun sourceBound sourceData =>
      Exists.elim
        sourceData
        (fun sourceComplex sourceComplexData =>
          And.elim
            sourceComplexData
            (fun _ sourceSupportAndEq =>
              And.elim
                sourceSupportAndEq
                (fun sourceSupport sourceEq =>
                  Exists.elim
                    target_mem
                    (fun targetBound targetData =>
                      Exists.elim
                        targetData
                        (fun targetComplex targetComplexData =>
                          And.elim
                            targetComplexData
                            (fun _ targetSupportAndEq =>
                              And.elim
                                targetSupportAndEq
                                (fun targetSupport targetEq =>
                                  let sourceObject :
                                      TraceAnalyticDMgmComparisonSource :=
                                    TraceAnalyticDMgmComparisonSource.objectOf
                                      (TraceAnalyticAdditiveHomotopyCategory
                                        .objectOf sourceComplex)
                                  let targetObject :
                                      TraceAnalyticDMgmComparisonSource :=
                                    TraceAnalyticDMgmComparisonSource.objectOf
                                      (TraceAnalyticAdditiveHomotopyCategory
                                        .objectOf targetComplex)
                                  let concreteHom : sourceObject ⟶ targetObject :=
                                    eqToHom (Eq.symm sourceEq) ≫
                                      hom ≫
                                        eqToHom targetEq
                                  Exists.elim
                                    (TraceAnalyticDMgmComparisonSource
                                      .exists_leftFraction concreteHom)
                                    (fun fraction fraction_eq =>
                                      let fraction_zero :
                                          fraction.map
                                              TraceAnalyticDMgmComparisonSource
                                                .quotientFunctor
                                              (CategoryTheory.Localization
                                                .inverts
                                                TraceAnalyticDMgmComparisonSource
                                                  .quotientFunctor
                                                TraceAnalyticStableNullSubcategory
                                                  .invertedMorphisms) =
                                            0 :=
                                        TraceAnalyticDMgmComparisonSource
                                          .DegreewiseBoundedStable
                                          .leftFraction_map_zero_of_supported_concrete_numerator_target
                                            (Nonempty.some sourceSupport)
                                            (Nonempty.some targetSupport)
                                            fraction
                                      let concreteHom_zero :
                                          concreteHom =
                                            (0 : sourceObject ⟶ targetObject) :=
                                        Eq.trans fraction_eq fraction_zero
                                      TraceAnalyticDMgmComparisonSource
                                        .DegreewiseBoundedStable
                                        .ambient_hom_eq_zero_of_iso_conjugate_eq_zero
                                          (eqToIso sourceEq)
                                          (eqToIso targetEq)
                                          hom
                                          concreteHom_zero))))))))))

/-- Support-based orthogonality in the degreewise bounded stable source. -/
theorem supportTStructure_zero
    {source target : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 target) :
    hom = 0 :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructure_zero_of_supportedAmbient_zero
      (fun sourceConcreteMem targetConcreteMem concreteHom =>
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportedAmbient_zero
            sourceConcreteMem
            targetConcreteMem
            concreteHom)
      hom
      source_mem
      target_mem

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
