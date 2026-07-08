import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.BoundedRoof.InternalSpan.DenominatorIso.Solved.Owner

/-!
# Unconjugated solved internal bounded roof spans

This file removes the representative-isomorphism conjugation from the solved
internal bounded roof formula.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The solved internal bounded roof formula can be written for the original
bounded-stable morphism itself. -/
theorem exists_internalRepresentativeBoundedRoofSpan_solved_unconjugated
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    ∃ (sourceBound : Nat),
      ∃ (sourceComplex : TraceAnalyticAdditiveCochainComplex),
        ∃ (targetBound : Nat),
          ∃ (targetComplex : TraceAnalyticAdditiveCochainComplex),
            ∃ (sourceRepresentative :
              TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
              ∃ (targetRepresentative :
                TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
                ∃ (roof :
                  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
                  ∃ (sourceIso :
                    sourceRepresentative.object ≅ source.object),
                    ∃ (targetIso :
                      targetRepresentative.object ≅ target.object),
                      ∃ (denominator :
                        targetRepresentative ⟶ roof),
                        ∃ (_ : IsIso denominator),
                          ∃ (numerator :
                            sourceRepresentative ⟶ roof),
                            morphism =
                              sourceIso.inv ≫ numerator ≫
                                inv denominator ≫ targetIso.hom :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_internalRepresentativeBoundedRoofSpan_solved morphism)
    (fun sourceBound sourceData =>
      Exists.elim
        sourceData
        (fun sourceComplex targetBoundData =>
          Exists.elim
            targetBoundData
            (fun targetBound targetData =>
              Exists.elim
                targetData
                (fun targetComplex sourceRepresentativeData =>
                  Exists.elim
                    sourceRepresentativeData
                    (fun sourceRepresentative targetRepresentativeData =>
                      Exists.elim
                        targetRepresentativeData
                        (fun targetRepresentative roofData =>
                          Exists.elim
                            roofData
                            (fun roof sourceIsoData =>
                              Exists.elim
                                sourceIsoData
                                (fun sourceIso targetIsoData =>
                                  Exists.elim
                                    targetIsoData
                                    (fun targetIso denominatorData =>
                                      Exists.elim
                                        denominatorData
                                        (fun denominator
                                          denominatorIsoData =>
                                          Exists.elim
                                            denominatorIsoData
                                            (fun denominatorIso
                                              numeratorData =>
                                              Exists.elim
                                                numeratorData
                                                (fun numerator solved =>
                                                  letI denominatorIsoField :
                                                      IsIso denominator :=
                                                    denominatorIso
                                                  let solvedAfterSource :
                                                      morphism ≫
                                                          targetIso.inv =
                                                        sourceIso.inv ≫
                                                          (numerator ≫
                                                            inv denominator) :=
                                                    (Iso.inv_comp_eq
                                                      sourceIso).mp
                                                      solved
                                                  let solvedReverse :
                                                      sourceIso.inv ≫
                                                            (numerator ≫
                                                              inv denominator) ≫
                                                          targetIso.hom =
                                                        morphism :=
                                                    (Iso.eq_comp_inv
                                                      targetIso).mp
                                                      (Eq.symm
                                                        solvedAfterSource)
                                                  let reassociated :
                                                      sourceIso.inv ≫
                                                            numerator ≫
                                                          inv denominator ≫
                                                        targetIso.hom =
                                                        sourceIso.inv ≫
                                                            (numerator ≫
                                                              inv denominator) ≫
                                                          targetIso.hom :=
                                                    Eq.trans
                                                      (Category.assoc
                                                        sourceIso.inv
                                                        numerator
                                                        (inv denominator ≫
                                                          targetIso.hom))
                                                      (congrArg
                                                        (fun arrow =>
                                                          sourceIso.inv ≫
                                                            arrow)
                                                        (Eq.symm
                                                          (Category.assoc
                                                            numerator
                                                            (inv denominator)
                                                            targetIso.hom)))
                                                  let unconjugated :
                                                      morphism =
                                                        sourceIso.inv ≫
                                                            numerator ≫
                                                          inv denominator ≫
                                                        targetIso.hom :=
                                                    Eq.symm
                                                      (Eq.trans
                                                        reassociated
                                                        solvedReverse)
                                                  Exists.intro
                                                    sourceBound
                                                    (Exists.intro
                                                      sourceComplex
                                                      (Exists.intro
                                                        targetBound
                                                        (Exists.intro
                                                          targetComplex
                                                          (Exists.intro
                                                            sourceRepresentative
                                                            (Exists.intro
                                                              targetRepresentative
                                                              (Exists.intro
                                                                roof
                                                                (Exists.intro
                                                                  sourceIso
                                                                  (Exists.intro
                                                                    targetIso
                                                                    (Exists.intro
                                                                      denominator
                                                                      (Exists.intro
                                                                        denominatorIso
                                                                        (Exists.intro
                                                                          numerator
                                                                          unconjugated)))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
