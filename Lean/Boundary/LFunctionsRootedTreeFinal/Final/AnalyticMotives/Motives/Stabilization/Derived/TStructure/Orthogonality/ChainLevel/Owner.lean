import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Algebra.Homology.QuasiIso
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Owner

/-!
# Chain-level orthogonality for represented derived analytic motives

This file owns the represented-complex form of adjacent homological
orthogonality.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The denominator of a derived left fraction transports lower exactness to
the auxiliary target complex. -/
theorem leftFraction_auxiliary_exactAt_below
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceComplex targetComplex)
    (targetExact :
      ∀ degree : ℤ,
        degree < 1 →
          targetComplex.ExactAt degree) :
    ∀ degree : ℤ,
      degree < 1 →
        fraction.Y'.ExactAt degree :=
  fun degree degree_lt_one =>
    let denominatorQuasiIso : QuasiIso fraction.s :=
      (HomologicalComplex.mem_quasiIso_iff fraction.s).mp
        fraction.hs
    letI : QuasiIso fraction.s := denominatorQuasiIso
    (_root_.quasiIsoAt_iff_exactAt
      fraction.s
      degree
      (targetExact degree degree_lt_one)).mp
      inferInstance

/-- A left fraction maps to zero if its numerator maps to zero. -/
theorem leftFraction_maps_to_zero_of_numerator_maps_to_zero
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceComplex targetComplex)
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

/-- A left fraction whose denominator is a quasi-isomorphism into a target
bounded below across the adjacent gap maps to zero in the derived category. -/
theorem exactAtBounds_leftFraction_maps_to_zero
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceComplex targetComplex)
    (sourceExact :
      ∀ degree : ℤ,
        0 < degree →
          sourceComplex.ExactAt degree)
    (targetExact :
      ∀ degree : ℤ,
        degree < 1 →
          targetComplex.ExactAt degree) :
    fraction.map
        TraceAnalyticDerivedMotiveCategory.localizationFunctor
        (Localization.inverts
          TraceAnalyticDerivedMotiveCategory.localizationFunctor
          TraceAnalyticDerivedMotiveCategory.derivedQuasiIsoClass) =
      0 :=
  TraceAnalyticDerivedMotiveCategory
    .leftFraction_maps_to_zero_of_numerator_maps_to_zero
      sourceComplex
      targetComplex
      fraction
      (TraceAnalyticDerivedMotiveCategory
        .exactAtBounds_leftFraction_numerator_maps_to_zero
          sourceComplex
          targetComplex
          fraction
          sourceExact
          (TraceAnalyticDerivedMotiveCategory
            .leftFraction_auxiliary_exactAt_below
              sourceComplex
              targetComplex
              fraction
              targetExact))


/-- Every represented derived morphism admits a left-fraction representative
over the quasi-isomorphism localization. -/
theorem exists_leftFraction_for_objectOf_morphism
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (morphism :
      TraceAnalyticDerivedMotiveCategory.objectOf sourceComplex ⟶
        TraceAnalyticDerivedMotiveCategory.objectOf targetComplex) :
    ∃ fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceComplex targetComplex,
      morphism =
        fraction.map
          TraceAnalyticDerivedMotiveCategory.localizationFunctor
          (Localization.inverts
            TraceAnalyticDerivedMotiveCategory.localizationFunctor
            TraceAnalyticDerivedMotiveCategory.derivedQuasiIsoClass) :=
  Localization.exists_leftFraction
    TraceAnalyticDerivedMotiveCategory.localizationFunctor
    TraceAnalyticDerivedMotiveCategory.derivedQuasiIsoClass
    morphism

/-- A represented derived morphism is zero once one left-fraction
representative maps to zero. -/
theorem objectOf_morphism_eq_zero_of_leftFraction_maps_to_zero
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (morphism :
      TraceAnalyticDerivedMotiveCategory.objectOf sourceComplex ⟶
        TraceAnalyticDerivedMotiveCategory.objectOf targetComplex)
    (fraction :
      TraceAnalyticDerivedMotiveCategory
        .DerivedLeftFraction sourceComplex targetComplex)
    (fractionRepresents :
      morphism =
        fraction.map
          TraceAnalyticDerivedMotiveCategory.localizationFunctor
          (Localization.inverts
            TraceAnalyticDerivedMotiveCategory.localizationFunctor
            TraceAnalyticDerivedMotiveCategory.derivedQuasiIsoClass))
    (fractionZero :
      fraction.map
          TraceAnalyticDerivedMotiveCategory.localizationFunctor
          (Localization.inverts
            TraceAnalyticDerivedMotiveCategory.localizationFunctor
            TraceAnalyticDerivedMotiveCategory.derivedQuasiIsoClass) =
        0) :
    morphism = 0 :=
  Eq.trans fractionRepresents fractionZero

/-- Chain-level adjacent exactness bounds kill represented derived morphisms. -/
theorem exactAtBounds_objectOf_morphism_eq_zero
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (morphism :
      TraceAnalyticDerivedMotiveCategory.objectOf sourceComplex ⟶
        TraceAnalyticDerivedMotiveCategory.objectOf targetComplex)
    (sourceExact :
      ∀ degree : ℤ,
        0 < degree →
          sourceComplex.ExactAt degree)
    (targetExact :
      ∀ degree : ℤ,
        degree < 1 →
          targetComplex.ExactAt degree) :
    morphism = 0 :=
  Exists.elim
    (TraceAnalyticDerivedMotiveCategory
      .exists_leftFraction_for_objectOf_morphism
        sourceComplex
        targetComplex
        morphism)
    (fun fraction fractionRepresents =>
      TraceAnalyticDerivedMotiveCategory
        .objectOf_morphism_eq_zero_of_leftFraction_maps_to_zero
          sourceComplex
          targetComplex
          morphism
          fraction
          fractionRepresents
          (TraceAnalyticDerivedMotiveCategory
            .exactAtBounds_leftFraction_maps_to_zero
              sourceComplex
              targetComplex
              fraction
              sourceExact
              targetExact))

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
