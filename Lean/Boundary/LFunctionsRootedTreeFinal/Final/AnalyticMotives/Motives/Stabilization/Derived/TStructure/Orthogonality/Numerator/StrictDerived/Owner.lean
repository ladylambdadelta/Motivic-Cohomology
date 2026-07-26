import Mathlib.Algebra.Homology.QuasiIso
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.StrictSupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.Owner

/-!
# Strict derived numerator orthogonality

This file owns the left-fraction form of orthogonality between strict lower
and strict upper representatives.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The numerator of a left fraction from strict lower support to strict upper
support maps to zero after localization. -/
theorem strictSupport_leftFraction_numerator_maps_to_zero
    (sourceReplacement targetReplacement :
      TraceAnalyticAbelianCochainComplex)
    [sourceReplacement.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncLEEmbedding 0)]
    [targetReplacement.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)]
    (fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceReplacement targetReplacement) :
    TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        fraction.f =
      0 :=
  let auxiliaryReplacement : TraceAnalyticAbelianCochainComplex :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGE 1 fraction.Y'
  let auxiliaryProjection :
      fraction.Y' ⟶ auxiliaryReplacement :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGEProjectionMap 1 fraction.Y'
  let targetExact :
      ∀ degree : ℤ,
        degree < 1 →
          targetReplacement.ExactAt degree :=
    fun degree degree_lt_one =>
      targetReplacement.exactAt_of_isSupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
        degree
        (fun upperTail =>
          TraceAnalyticDerivedMotiveCategory
            .truncGEEmbedding_outside_below_cut
              1
              degree
              degree_lt_one
              upperTail)
  let denominatorQuasiIso : QuasiIso fraction.s :=
    (HomologicalComplex.mem_quasiIso_iff fraction.s).mp
      fraction.hs
  letI : QuasiIso fraction.s := denominatorQuasiIso
  let auxiliaryExact :
      ∀ degree : ℤ,
        degree < 1 →
          fraction.Y'.ExactAt degree :=
    fun degree degree_lt_one =>
      (_root_.quasiIsoAt_iff_exactAt
        fraction.s
        degree
        (targetExact degree degree_lt_one)).mp
        inferInstance
  letI :
      auxiliaryReplacement.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1) :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGE_isStrictlySupported 1 fraction.Y'
  letI : QuasiIso auxiliaryProjection :=
    TraceAnalyticDerivedMotiveCategory
      .exactAt_target_truncGEProjection_quasiIso
        fraction.Y'
        auxiliaryExact
  letI :
      IsIso
        (TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
          auxiliaryProjection) :=
    TraceAnalyticDerivedMotiveCategory
      .mapOf_isIso_of_quasiIso auxiliaryProjection
  let compositeZero :
      fraction.f ≫ auxiliaryProjection = 0 :=
    TraceAnalyticDerivedMotiveCategory
      .truncLE_zero_to_truncGE_one_hom_eq_zero
        sourceReplacement
        auxiliaryReplacement
        (fraction.f ≫ auxiliaryProjection)
  let compositeMapZero :
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
          (fraction.f ≫ auxiliaryProjection) =
        0 :=
    Eq.trans
      (congrArg
        (fun hom =>
          TraceAnalyticDerivedMotiveCategory.localizationFunctor.map hom)
        compositeZero)
      (TraceAnalyticDerivedMotiveCategory.localizationFunctor.map_zero
        sourceReplacement
        auxiliaryReplacement)
  let mapCompZero :
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
          fraction.f ≫
        TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
          auxiliaryProjection =
      0 :=
    Eq.trans
      (Eq.symm
        (TraceAnalyticDerivedMotiveCategory.localizationFunctor.map_comp
          fraction.f
          auxiliaryProjection))
      compositeMapZero
  (IsIso.comp_right_eq_zero
    (f :=
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        fraction.f)
    (g :=
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
        auxiliaryProjection)).mp
    mapCompZero

/-- A strict-support left fraction maps to zero if its numerator maps to zero. -/
theorem strictSupport_leftFraction_maps_to_zero_of_numerator_maps_to_zero
    (sourceReplacement targetReplacement :
      TraceAnalyticAbelianCochainComplex)
    (fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceReplacement targetReplacement)
    (numeratorZero :
      TraceAnalyticDerivedMotiveCategory.localizationFunctor.map
          fraction.f =
        0) :
    fraction.map
        TraceAnalyticDerivedMotiveCategory.localizationFunctor
        (Localization.inverts
          TraceAnalyticDerivedMotiveCategory.localizationFunctor
          TraceAnalyticDerivedMotiveCategory.derivedQuasiIsoClass) =
      0 :=
  Eq.trans
    (MorphismProperty.LeftFraction.map_eq
      fraction
      TraceAnalyticDerivedMotiveCategory.localizationFunctor)
    (Eq.trans
      (congrArg
        (fun numeratorMap =>
          numeratorMap ≫
            (Localization.isoOfHom
              TraceAnalyticDerivedMotiveCategory.localizationFunctor
              TraceAnalyticDerivedMotiveCategory.derivedQuasiIsoClass
              fraction.s
              fraction.hs).inv)
        numeratorZero)
      (zero_comp
        (Localization.isoOfHom
          TraceAnalyticDerivedMotiveCategory.localizationFunctor
          TraceAnalyticDerivedMotiveCategory.derivedQuasiIsoClass
          fraction.s
          fraction.hs).inv))

/-- Every derived morphism from a strict lower representative to a strict upper
representative is zero. -/
theorem strictSupport_objectOf_morphism_eq_zero
    (sourceReplacement targetReplacement :
      TraceAnalyticAbelianCochainComplex)
    [sourceReplacement.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncLEEmbedding 0)]
    [targetReplacement.IsStrictlySupported
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)]
    (morphism :
      TraceAnalyticDerivedMotiveCategory.objectOf sourceReplacement ⟶
        TraceAnalyticDerivedMotiveCategory.objectOf targetReplacement) :
    morphism = 0 :=
  Exists.elim
    (Localization.exists_leftFraction
      TraceAnalyticDerivedMotiveCategory.localizationFunctor
      TraceAnalyticDerivedMotiveCategory.derivedQuasiIsoClass
      morphism)
    (fun fraction fractionRepresents =>
      Eq.trans
        fractionRepresents
        (TraceAnalyticDerivedMotiveCategory
          .strictSupport_leftFraction_maps_to_zero_of_numerator_maps_to_zero
            sourceReplacement
            targetReplacement
            fraction
            (TraceAnalyticDerivedMotiveCategory
              .strictSupport_leftFraction_numerator_maps_to_zero
                sourceReplacement
                targetReplacement
                fraction)))

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
