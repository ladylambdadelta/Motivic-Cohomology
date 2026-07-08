import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Reindexed.Owner

/-!
# Iso-closure transport for Mathlib-facing orthogonality

This file proves the iso-closure bookkeeping for the Mathlib `TStructure.zero'`
field.  Once vanishing is known for the concrete representative predicates,
vanishing follows for the iso-closed Mathlib-facing predicates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Conjugating a zero representative morphism across source and target
isomorphisms gives the original morphism as zero. -/
theorem mathlib_orthogonality_of_conjugate_zero
    {source target sourceRepresentative targetRepresentative :
      TraceAnalyticDMgmComparisonSource}
    (sourceIso : source ≅ sourceRepresentative)
    (targetIso : target ≅ targetRepresentative)
    (hom : source ⟶ target)
    (conjugate_zero :
      sourceIso.inv ≫ hom ≫ targetIso.hom = 0) :
    hom = 0 :=
  calc
    hom =
        (hom ≫ targetIso.hom) ≫ targetIso.inv :=
      Eq.symm
        (Eq.trans
          (Category.assoc hom targetIso.hom targetIso.inv)
          (Eq.trans
            (congrArg
              (fun right => hom ≫ right)
              targetIso.hom_inv_id)
            (Category.comp_id hom)))
    _ =
        ((sourceIso.hom ≫ sourceIso.inv) ≫ hom ≫ targetIso.hom) ≫
          targetIso.inv :=
      Eq.symm
        (Eq.trans
          (congrArg
            (fun left => (left ≫ hom ≫ targetIso.hom) ≫ targetIso.inv)
            sourceIso.hom_inv_id)
          (congrArg
            (fun middle => (middle ≫ targetIso.hom) ≫ targetIso.inv)
            (Category.id_comp hom)))
    _ =
        (sourceIso.hom ≫ (sourceIso.inv ≫ hom ≫ targetIso.hom)) ≫
          targetIso.inv :=
      congrArg
        (fun middle => middle ≫ targetIso.inv)
        (Eq.trans
          (Category.assoc (sourceIso.hom ≫ sourceIso.inv) hom targetIso.hom)
          (congrArg
            (fun middle => middle ≫ targetIso.hom)
            (Category.assoc sourceIso.hom sourceIso.inv hom)))
    _ = (sourceIso.hom ≫ 0) ≫ targetIso.inv :=
      congrArg
        (fun middle => (sourceIso.hom ≫ middle) ≫ targetIso.inv)
        conjugate_zero
    _ = 0 :=
      Eq.trans
        (congrArg
          (fun middle => middle ≫ targetIso.inv)
          (Category.comp_zero sourceIso.hom))
        (Category.zero_comp targetIso.inv)

/-- Representative-level orthogonality implies the Mathlib-facing iso-closed
`zero'` field. -/
theorem mathlib_zero_of_representative_zero
    (representative_zero :
      ∀ {source target : TraceAnalyticDMgmComparisonSource}
        (hom : source ⟶ target),
        TraceAnalyticMotivicTStructure.coaisleGE (-0) source →
        TraceAnalyticMotivicTStructure.aisleLE (-1) target →
        hom = 0)
    {source target : TraceAnalyticDMgmComparisonSource}
    (hom : source ⟶ target)
    (source_mem : TraceAnalyticMotivicTStructure.mathlibLE 0 source)
    (target_mem : TraceAnalyticMotivicTStructure.mathlibGE 1 target) :
    hom = 0 :=
  Exists.elim
    source_mem
    (fun sourceRepresentative sourceData =>
      Exists.elim
        sourceData
        (fun sourceRepresentativeMem sourceIsoData =>
          Nonempty.elim
            sourceIsoData
            (fun sourceIso =>
              Exists.elim
                target_mem
                (fun targetRepresentative targetData =>
                  Exists.elim
                    targetData
                    (fun targetRepresentativeMem targetIsoData =>
                      Nonempty.elim
                        targetIsoData
                        (fun targetIso =>
                          TraceAnalyticMotivicTStructure
                            .mathlib_orthogonality_of_conjugate_zero
                              sourceIso
                              targetIso
                              hom
                              (representative_zero
                                (sourceIso.inv ≫ hom ≫ targetIso.hom)
                                sourceRepresentativeMem
                                targetRepresentativeMem))))))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
