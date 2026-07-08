import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.BoundedRoof.InternalSpan.DenominatorIso.Owner

/-!
# Solved internal bounded roof spans

This file converts the internal roof equation with isomorphism denominator into
the solved morphism formula obtained by composing with the denominator inverse.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A morphism in the degreewise bounded stable source is represented, after
choosing concrete source and target representatives, by a numerator followed by
the inverse of an internal isomorphism denominator. -/
theorem exists_internalRepresentativeBoundedRoofSpan_solved
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
                            sourceIso.hom ≫ morphism ≫ targetIso.inv =
                              numerator ≫ inv denominator :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_internalRepresentativeBoundedRoofSpan_denominatorIso
      morphism)
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
                                                (fun numerator
                                                  roofEquation =>
                                                  letI denominatorIsoField :
                                                      IsIso denominator :=
                                                    denominatorIso
                                                  let conjugated :
                                                      sourceRepresentative
                                                          .object ⟶
                                                        targetRepresentative
                                                          .object :=
                                                    sourceIso.hom ≫
                                                      morphism ≫
                                                        targetIso.inv
                                                  let solvedReverse :
                                                      numerator ≫
                                                          inv denominator =
                                                        conjugated :=
                                                    (Iso.comp_inv_eq
                                                      (asIso
                                                        denominator)).mpr
                                                      roofEquation.symm
                                                  let solved :
                                                      conjugated =
                                                        numerator ≫
                                                          inv denominator :=
                                                    Eq.symm solvedReverse
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
                                                                          solved)))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
