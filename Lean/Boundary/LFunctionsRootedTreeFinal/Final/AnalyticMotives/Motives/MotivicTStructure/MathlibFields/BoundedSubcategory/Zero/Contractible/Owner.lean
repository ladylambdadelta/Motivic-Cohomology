import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Zero.Representative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Contractible.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Preadditive.Owner

/-!
# Contractibility of the concrete zero bounded complex

The zero bounded representative comes from the concrete zero cochain complex.
This file proves that this concrete complex is contractible in the homotopy
category, hence its homotopy-category image is a zero object.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open HomologicalComplex

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The identity endomorphism of the concrete zero complex equals the zero
endomorphism. -/
theorem zeroConcrete_id_eq_zero :
    (𝟙 TraceAnalyticAdditiveCochainComplex.zeroConcrete) =
      (0 :
        TraceAnalyticAdditiveCochainComplex.zeroConcrete ⟶
          TraceAnalyticAdditiveCochainComplex.zeroConcrete) :=
  HomologicalComplex.hom_ext
    (𝟙 TraceAnalyticAdditiveCochainComplex.zeroConcrete)
    (0 :
      TraceAnalyticAdditiveCochainComplex.zeroConcrete ⟶
        TraceAnalyticAdditiveCochainComplex.zeroConcrete)
    (fun degree =>
      TraceAnalyticAdditiveCategory.hom_to_zero_ext
        TraceAnalyticAdditiveCategory.zeroObject
        ((𝟙 TraceAnalyticAdditiveCochainComplex.zeroConcrete).f degree)
        ((0 :
          TraceAnalyticAdditiveCochainComplex.zeroConcrete ⟶
            TraceAnalyticAdditiveCochainComplex.zeroConcrete).f degree))

/-- The concrete zero complex is contractible in the homotopy category. -/
theorem zeroConcrete_contractible :
    Nonempty
      (Homotopy
        (𝟙 TraceAnalyticAdditiveCochainComplex.zeroConcrete)
        0) :=
  Nonempty.intro
    (Homotopy.ofEq
      TraceAnalyticDMgmComparisonSource.BoundedStable
        .zeroConcrete_id_eq_zero)

/-- The homotopy-category image of the concrete zero complex is a zero
object. -/
theorem zeroConcrete_homotopyObject_isZero :
    IsZero
      (TraceAnalyticAdditiveHomotopyCategory.objectOf
        TraceAnalyticAdditiveCochainComplex.zeroConcrete) :=
  TraceAnalyticAdditiveHomotopyCategory.isZero_objectOf_of_contractible
    TraceAnalyticAdditiveCochainComplex.zeroConcrete
    TraceAnalyticDMgmComparisonSource.BoundedStable
      .zeroConcrete_contractible

/-- The homotopy object represented by the zero bounded complex is a zero
object. -/
theorem sourceZeroWeightBoundedHomotopyObject_isZero
    (bound : Nat) :
    IsZero
      (TraceAnalyticMotiveComparison
        .sourceZeroWeightBoundedHomotopyObject bound) :=
  Eq.subst
    (motive := fun object =>
      IsZero object)
    (Eq.symm
      (TraceAnalyticMotiveComparison
        .sourceZeroWeightBoundedHomotopyObject_eq bound))
    TraceAnalyticDMgmComparisonSource.BoundedStable
      .zeroConcrete_homotopyObject_isZero

/-- The stable comparison-source object represented by the zero bounded
complex is a zero object. -/
theorem sourceZeroStableWeightBoundedObject_isZero
    (bound : Nat) :
    IsZero
      (TraceAnalyticMotiveComparison
        .sourceZeroStableWeightBoundedObject bound) :=
  letI stableHasZeroObject :
      HasZeroObject TraceAnalyticDMgmComparisonSource :=
    TraceAnalyticDMgmComparisonSource.quotientFunctor
      .hasZeroObject_of_additive
  Eq.subst
    (motive := fun object =>
      IsZero object)
    (Eq.symm
      (TraceAnalyticMotiveComparison
        .sourceZeroStableWeightBoundedObject_eq bound))
    (CategoryTheory.Limits.map_isZero
      TraceAnalyticDMgmComparisonSource.quotientFunctor
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .sourceZeroWeightBoundedHomotopyObject_isZero bound))

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
