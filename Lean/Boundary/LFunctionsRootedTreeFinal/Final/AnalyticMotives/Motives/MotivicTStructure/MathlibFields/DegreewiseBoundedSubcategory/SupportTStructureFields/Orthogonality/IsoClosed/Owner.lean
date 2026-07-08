import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Owner

/-!
# Iso-closed support orthogonality reduction

This file removes the isomorphism-closure layer from support orthogonality.
Once concrete ambient lower-to-upper support morphisms vanish, the corresponding
iso-closed support morphisms in the degreewise bounded stable source vanish by
conjugating through the two representative isomorphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Vanishing of a conjugated ambient morphism implies vanishing of the original
degreewise-bounded full-subcategory morphism. -/
theorem hom_eq_zero_of_iso_conjugate_eq_zero
    {source target : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    {sourceRepresentative targetRepresentative :
      TraceAnalyticDMgmComparisonSource}
    (sourceIso : source.object ≅ sourceRepresentative)
    (targetIso : target.object ≅ targetRepresentative)
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
        (0 : source.object ⟶ targetRepresentative) :=
    Eq.trans
      source_cancelled
      (Category.comp_zero sourceIso.hom)
  let target_right_cancel :
      (hom ≫ targetIso.hom) ≫ targetIso.inv =
        (0 : source.object ⟶ targetRepresentative) ≫ targetIso.inv :=
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

/-- Concrete ambient support orthogonality implies iso-closed support
orthogonality in the degreewise bounded stable source. -/
theorem supportTStructure_zero_of_supportedAmbient_zero
    (ambient_zero :
      ∀ {source target : TraceAnalyticDMgmComparisonSource},
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportedLEAmbient 0 source →
          TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
              .supportedGEAmbient 1 target →
            (hom : source ⟶ target) →
              hom = 0)
    {source target : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (hom : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 target) :
    hom = 0 :=
  Exists.elim
    source_mem
    (fun sourceRepresentative sourceRepresentativeData =>
      Exists.elim
        sourceRepresentativeData
        (fun sourceConcreteMem sourceIsoData =>
          Nonempty.elim
            sourceIsoData
            (fun sourceIso =>
              Exists.elim
                target_mem
                (fun targetRepresentative targetRepresentativeData =>
                  Exists.elim
                    targetRepresentativeData
                    (fun targetConcreteMem targetIsoData =>
                      Nonempty.elim
                        targetIsoData
                        (fun targetIso =>
                          TraceAnalyticDMgmComparisonSource
                            .DegreewiseBoundedStable
                            .hom_eq_zero_of_iso_conjugate_eq_zero
                              sourceIso
                              targetIso
                              hom
                              (ambient_zero
                                sourceConcreteMem
                                targetConcreteMem
                                (sourceIso.inv ≫ hom ≫
                                  targetIso.hom)))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
