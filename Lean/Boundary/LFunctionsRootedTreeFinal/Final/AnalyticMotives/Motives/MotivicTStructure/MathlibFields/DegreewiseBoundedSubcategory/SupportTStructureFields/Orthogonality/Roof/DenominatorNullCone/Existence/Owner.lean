import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Orthogonality.Roof.DenominatorNullCone.Owner

/-!
# Existence form of null-cone roof orthogonality reduction

This file combines the unconjugated null-cone solved roof presentation with
the roof-level support orthogonality reduction.  It packages the analytic roof
data for a morphism and leaves only the concrete numerator-vanishing step.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Every support-bounded morphism has a null-cone solved roof presentation
whose numerator-zero condition implies that the original morphism is zero. -/
theorem exists_nullConeSolvedRoof_support_numerator_zero_reduction
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 target) :
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
              ∃ (denominator : targetRepresentative ⟶ roof),
                ∃ (numerator : sourceRepresentative ⟶ roof),
                  ∃ (targetComplex :
                    TraceAnalyticAdditiveCochainComplex),
                    ∃ (roofVertex :
                      TraceAnalyticAdditiveHomotopyCategory),
                      ∃ (roof_eq :
                        roof.object =
                          TraceAnalyticDMgmComparisonSource.objectOf
                            roofVertex),
                        ∃ (rawDenominator :
                          TraceAnalyticAdditiveHomotopyCategory.objectOf
                              targetComplex ⟶ roofVertex),
                          ∃ (denominatorCone :
                            TraceAnalyticAdditiveHomotopyCategory),
                            ∃ (denominatorCoconeMap :
                              roofVertex ⟶ denominatorCone),
                              ∃ (denominatorBoundary :
                                denominatorCone ⟶
                                  (TraceAnalyticAdditiveHomotopyCategory
                                    .objectOf targetComplex)⟦(1 : ℤ)⟧),
                                ∃ (_ :
                                  Triangle.mk
                                      rawDenominator
                                      denominatorCoconeMap
                                      denominatorBoundary ∈
                                    TraceAnalyticAdditiveHomotopyCategory
                                      .distinguishedTriangles),
                                  ∃ (_ :
                                    TraceAnalyticStableNullSubcategory.P
                                      denominatorCone),
                                    ∃ (_ :
                                      denominator =
                                        TraceAnalyticDMgmComparisonSource
                                            .quotientFunctor.map
                                            rawDenominator ≫
                                          eqToHom (Eq.symm roof_eq)),
                                      ∃ (_ :
                                        morphism =
                                          sourceIso.inv ≫ numerator ≫
                                            inv denominator ≫
                                            targetIso.hom),
                                        numerator = 0 → morphism = 0 :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_internalRepresentativeBoundedRoofSpan_denominatorNullCone_solved_unconjugated
        morphism)
    (fun _ sourceBoundData =>
      Exists.elim
        sourceBoundData
        (fun _ targetBoundData =>
          Exists.elim
            targetBoundData
            (fun _ targetComplexData =>
              Exists.elim
                targetComplexData
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
                                        (fun denominator denominatorIsoData =>
                                          Exists.elim
                                            denominatorIsoData
                                            (fun _ numeratorData =>
                                              Exists.elim
                                                numeratorData
                                                (fun numerator roofVertexData =>
                                                  Exists.elim
                                                    roofVertexData
                                                    (fun roofVertex roofEqData =>
                                                      Exists.elim
                                                        roofEqData
                                                        (fun roof_eq rawDenominatorData =>
                                                          Exists.elim
                                                            rawDenominatorData
                                                            (fun rawDenominator
                                                              rawNumeratorData =>
                                                              Exists.elim
                                                                rawNumeratorData
                                                                (fun _ coneData =>
                                                                  Exists.elim
                                                                    coneData
                                                                    (fun denominatorCone
                                                                      coneMapData =>
                                                                      Exists.elim
                                                                        coneMapData
                                                                        (fun denominatorCoconeMap
                                                                          boundaryData =>
                                                                          Exists.elim
                                                                            boundaryData
                                                                            (fun denominatorBoundary
                                                                              distinguishedData =>
                                                                              Exists.elim
                                                                                distinguishedData
                                                                                (fun distinguished
                                                                                  nullData =>
                                                                                  Exists.elim
                                                                                    nullData
                                                                                    (fun null
                                                                                      equationData =>
                                                                                      And.elim
                                                                                        equationData
                                                                                        (fun denominator_eq
                                                                                          equationRest =>
                                                                                          And.elim
                                                                                            equationRest
                                                                                            (fun _ solved =>
                                                                                              let zeroReduction :
                                                                                                  numerator = 0 →
                                                                                                    morphism = 0 :=
                                                                                                fun numerator_zero =>
                                                                                                  TraceAnalyticDMgmComparisonSource
                                                                                                    .DegreewiseBoundedStable
                                                                                                    .hom_eq_zero_of_nullConeSolvedRoof_support_numerator_zero_of_denominator_eq
                                                                                                      sourceIso
                                                                                                      targetIso
                                                                                                      denominator
                                                                                                      numerator
                                                                                                      morphism
                                                                                                      roof_eq
                                                                                                      rawDenominator
                                                                                                      denominatorCoconeMap
                                                                                                      denominatorBoundary
                                                                                                      distinguished
                                                                                                      null
                                                                                                      denominator_eq
                                                                                                      solved
                                                                                                      source_mem
                                                                                                      target_mem
                                                                                                      numerator_zero
                                                                                              Exists.intro
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
                                                                                                            numerator
                                                                                                            (Exists.intro
                                                                                                              targetComplex
                                                                                                              (Exists.intro
                                                                                                                roofVertex
                                                                                                                (Exists.intro
                                                                                                                  roof_eq
                                                                                                                  (Exists.intro
                                                                                                                    rawDenominator
                                                                                                                    (Exists.intro
                                                                                                                      denominatorCone
                                                                                                                      (Exists.intro
                                                                                                                        denominatorCoconeMap
                                                                                                                        (Exists.intro
                                                                                                                          denominatorBoundary
                                                                                                                          (Exists.intro
                                                                                                                            distinguished
                                                                                                                            (Exists.intro
                                                                                                                              null
                                                                                                                              (Exists.intro
                                                                                                                                denominator_eq
                                                                                                                                (Exists.intro
                                                                                                                                  solved
                                                                                                                                  zeroReduction))))))))))))))))))))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
