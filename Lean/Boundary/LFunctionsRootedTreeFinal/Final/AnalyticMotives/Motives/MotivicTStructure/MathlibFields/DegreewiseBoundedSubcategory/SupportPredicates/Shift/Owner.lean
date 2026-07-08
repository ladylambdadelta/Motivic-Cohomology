import Mathlib.Tactic.Omega
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportPredicates.IsoClosure.Owner

/-!
# Shift closure for support predicates

This file proves that concrete lower-tail and upper-tail support presentations
are stable under the existing cochain shift and the induced stable shift on the
degreewise bounded source.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Lower-tail images shift by the same integer as cochain degrees. -/
theorem truncLEEmbedding_shift_image
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (index : ℕ) :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding sourceCut).f index =
      (TraceAnalyticMotivicTStructure.truncLEEmbedding targetCut).f index +
        shift := by
  omega

/-- Upper-tail images shift by the same integer as cochain degrees. -/
theorem truncGEEmbedding_shift_image
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (index : ℕ) :
    (TraceAnalyticMotivicTStructure.truncGEEmbedding sourceCut).f index =
      (TraceAnalyticMotivicTStructure.truncGEEmbedding targetCut).f index +
        shift := by
  omega

/-- A degree equality after adding the same shift cancels back to the target
degree. -/
theorem degree_eq_of_add_shift_eq
    {left right shift : ℤ}
    (eq : left + shift = right + shift) :
    left = right :=
  add_right_cancel eq

/-- Strict support transports through a cochain shift when the source
embedding is the target embedding translated by the shift. -/
def strictSupport_shift
    {index : Type*}
    {sourceShape targetShape : ComplexShape index}
    (sourceEmbedding :
      sourceShape.Embedding (ComplexShape.up ℤ))
    (targetEmbedding :
      targetShape.Embedding (ComplexShape.up ℤ))
    (complex : TraceAnalyticAdditiveCochainComplex)
    (shift : ℤ)
    (imageShift :
      ∀ index,
        sourceEmbedding.f index = targetEmbedding.f index + shift)
    (support : complex.IsStrictlySupported sourceEmbedding) :
    ((CochainComplex.shiftFunctor
      TraceAnalyticAdditiveCategoryObject
      shift).obj complex).IsStrictlySupported targetEmbedding where
  isZero :=
    fun degree targetComplement =>
      let sourceComplement :
          ∀ index, sourceEmbedding.f index ≠ degree + shift :=
        fun index sourceEq =>
          let targetPlusShiftEq :
              targetEmbedding.f index + shift = degree + shift :=
            Eq.trans (Eq.symm (imageShift index)) sourceEq
          let targetEq :
              targetEmbedding.f index = degree :=
            TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
              .degree_eq_of_add_shift_eq targetPlusShiftEq
          targetComplement index targetEq
      IsZero.of_iso
        (support.isZero (degree + shift) sourceComplement)
        (CochainComplex.shiftFunctorObjXIso
          complex
          shift
          degree
          (degree + shift)
          rfl).symm

/-- Concrete ambient lower-tail support is stable under ambient shifts. -/
theorem supportedLEAmbient_shift
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEAmbient sourceCut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedLEIsoClosedAmbient targetCut (object⟦shift⟧) :=
  Exists.elim
    membership
    (fun bound boundData =>
      Exists.elim
        boundData
        (fun complex complexData =>
          And.elim
            complexData
            (fun bounded supportAndObject =>
              And.elim
                supportAndObject
                (fun support objectEq =>
                  let shiftedComplex :
                      TraceAnalyticAdditiveCochainComplex :=
                    (CochainComplex.shiftFunctor
                      TraceAnalyticAdditiveCategoryObject
                      shift).obj complex
                  let shiftedRepresentative :
                      TraceAnalyticDMgmComparisonSource :=
                    TraceAnalyticDMgmComparisonSource.objectOf
                      (TraceAnalyticAdditiveHomotopyCategory.objectOf
                        shiftedComplex)
                  let shiftedMembership :
                      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                        .supportedLEAmbient targetCut shiftedRepresentative :=
                    Exists.intro
                      bound
                      (Exists.intro
                        shiftedComplex
                        (And.intro
                          (TraceAnalyticMotiveComparison
                            .sourceComplexDegreewiseIsoClosureBoundedBy_shift
                              bounded
                              shift)
                          (And.intro
                            (Nonempty.elim
                              support
                              (fun supportWitness =>
                                Nonempty.intro
                                  (TraceAnalyticDMgmComparisonSource
                                    .DegreewiseBoundedStable
                                    .strictSupport_shift
                                      (TraceAnalyticMotivicTStructure
                                        .truncLEEmbedding sourceCut)
                                      (TraceAnalyticMotivicTStructure
                                        .truncLEEmbedding targetCut)
                                      complex
                                      shift
                                      (TraceAnalyticDMgmComparisonSource
                                        .DegreewiseBoundedStable
                                        .truncLEEmbedding_shift_image
                                          sourceCut
                                          shift
                                          targetCut
                                          cut_eq)
                                      supportWitness)))
                            rfl)))
                  let homotopyShiftIso :
                      TraceAnalyticAdditiveHomotopyCategory.objectOf
                          shiftedComplex ≅
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          complex)⟦shift⟧ :=
                    (TraceAnalyticAdditiveHomotopyCategory
                      .quotientFunctor.commShiftIso shift).app complex
                  let stableShiftIso :
                      shiftedRepresentative ≅
                        (TraceAnalyticDMgmComparisonSource.objectOf
                          (TraceAnalyticAdditiveHomotopyCategory.objectOf
                            complex))⟦shift⟧ :=
                    TraceAnalyticStableMotiveCategory.quotientFunctor.mapIso
                        homotopyShiftIso ≪≫
                      TraceAnalyticStableMotiveCategory.objectOfShiftIso
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          complex)
                        shift
                  let objectShiftIso :
                      (TraceAnalyticDMgmComparisonSource.objectOf
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          complex))⟦shift⟧ ≅
                        object⟦shift⟧ :=
                    (CategoryTheory.shiftFunctor
                      TraceAnalyticDMgmComparisonSource
                      shift).mapIso
                        (eqToIso (Eq.symm objectEq))
                  CategoryTheory.mem_of_iso
                    (P := TraceAnalyticDMgmComparisonSource
                      .DegreewiseBoundedStable
                      .supportedLEIsoClosedAmbient targetCut)
                    (stableShiftIso ≪≫ objectShiftIso)
                    (CategoryTheory.le_isoClosure
                      (TraceAnalyticDMgmComparisonSource
                        .DegreewiseBoundedStable
                        .supportedLEAmbient targetCut)
                      shiftedRepresentative
                      shiftedMembership))))))

/-- Concrete ambient upper-tail support is stable under ambient shifts. -/
theorem supportedGEAmbient_shift
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (object : TraceAnalyticDMgmComparisonSource)
    (membership :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEAmbient sourceCut object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedGEIsoClosedAmbient targetCut (object⟦shift⟧) :=
  Exists.elim
    membership
    (fun bound boundData =>
      Exists.elim
        boundData
        (fun complex complexData =>
          And.elim
            complexData
            (fun bounded supportAndObject =>
              And.elim
                supportAndObject
                (fun support objectEq =>
                  let shiftedComplex :
                      TraceAnalyticAdditiveCochainComplex :=
                    (CochainComplex.shiftFunctor
                      TraceAnalyticAdditiveCategoryObject
                      shift).obj complex
                  let shiftedRepresentative :
                      TraceAnalyticDMgmComparisonSource :=
                    TraceAnalyticDMgmComparisonSource.objectOf
                      (TraceAnalyticAdditiveHomotopyCategory.objectOf
                        shiftedComplex)
                  let shiftedMembership :
                      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                        .supportedGEAmbient targetCut shiftedRepresentative :=
                    Exists.intro
                      bound
                      (Exists.intro
                        shiftedComplex
                        (And.intro
                          (TraceAnalyticMotiveComparison
                            .sourceComplexDegreewiseIsoClosureBoundedBy_shift
                              bounded
                              shift)
                          (And.intro
                            (Nonempty.elim
                              support
                              (fun supportWitness =>
                                Nonempty.intro
                                  (TraceAnalyticDMgmComparisonSource
                                    .DegreewiseBoundedStable
                                    .strictSupport_shift
                                      (TraceAnalyticMotivicTStructure
                                        .truncGEEmbedding sourceCut)
                                      (TraceAnalyticMotivicTStructure
                                        .truncGEEmbedding targetCut)
                                      complex
                                      shift
                                      (TraceAnalyticDMgmComparisonSource
                                        .DegreewiseBoundedStable
                                        .truncGEEmbedding_shift_image
                                          sourceCut
                                          shift
                                          targetCut
                                          cut_eq)
                                      supportWitness)))
                            rfl)))
                  let homotopyShiftIso :
                      TraceAnalyticAdditiveHomotopyCategory.objectOf
                          shiftedComplex ≅
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          complex)⟦shift⟧ :=
                    (TraceAnalyticAdditiveHomotopyCategory
                      .quotientFunctor.commShiftIso shift).app complex
                  let stableShiftIso :
                      shiftedRepresentative ≅
                        (TraceAnalyticDMgmComparisonSource.objectOf
                          (TraceAnalyticAdditiveHomotopyCategory.objectOf
                            complex))⟦shift⟧ :=
                    TraceAnalyticStableMotiveCategory.quotientFunctor.mapIso
                        homotopyShiftIso ≪≫
                      TraceAnalyticStableMotiveCategory.objectOfShiftIso
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          complex)
                        shift
                  let objectShiftIso :
                      (TraceAnalyticDMgmComparisonSource.objectOf
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          complex))⟦shift⟧ ≅
                        object⟦shift⟧ :=
                    (CategoryTheory.shiftFunctor
                      TraceAnalyticDMgmComparisonSource
                      shift).mapIso
                        (eqToIso (Eq.symm objectEq))
                  CategoryTheory.mem_of_iso
                    (P := TraceAnalyticDMgmComparisonSource
                      .DegreewiseBoundedStable
                      .supportedGEIsoClosedAmbient targetCut)
                    (stableShiftIso ≪≫ objectShiftIso)
                    (CategoryTheory.le_isoClosure
                      (TraceAnalyticDMgmComparisonSource
                        .DegreewiseBoundedStable
                        .supportedGEAmbient targetCut)
                      shiftedRepresentative
                      shiftedMembership))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
