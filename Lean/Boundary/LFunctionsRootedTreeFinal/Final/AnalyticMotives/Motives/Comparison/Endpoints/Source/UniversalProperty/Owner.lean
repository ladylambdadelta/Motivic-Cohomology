import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.StableHomotopyCategory.Owner

/-!
# Endpoint universal property of the comparison source

This file exposes the stable analytic Verdier quotient universal property at
comparison endpoint names: localization structure, functor equivalence, lift,
and lift factorization.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Endpoint form of the morphism property inverted by the comparison-source
quotient. -/
def TraceAnalyticMotiveComparison.sourceInvertedMorphisms :
    MorphismProperty TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticDMgmComparisonSource.invertedMorphisms

/-- Endpoint inverted morphisms are the stable analytic inverted morphisms. -/
theorem TraceAnalyticMotiveComparison.sourceInvertedMorphisms_eq_stable :
    TraceAnalyticMotiveComparison.sourceInvertedMorphisms =
      TraceAnalyticStableMotiveCategory.invertedMorphisms :=
  TraceAnalyticDMgmComparisonSource.invertedMorphisms_eq_stable

/-- Endpoint inverted morphisms are the stable homotopy comparison inverted
morphisms. -/
theorem TraceAnalyticMotiveComparison.sourceInvertedMorphisms_eq_stableHomotopy :
    TraceAnalyticMotiveComparison.sourceInvertedMorphisms =
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms :=
  rfl

/-- Endpoint form of the comparison-source localization structure. -/
def TraceAnalyticMotiveComparison.sourceIsLocalization :
    TraceAnalyticDMgmComparisonSource.quotientFunctor.IsLocalization
      TraceAnalyticMotiveComparison.sourceInvertedMorphisms :=
  TraceAnalyticDMgmComparisonSource.isLocalization

/-- Endpoint localization structure is the source owner localization
structure. -/
theorem TraceAnalyticMotiveComparison.sourceIsLocalization_eq_source :
    TraceAnalyticMotiveComparison.sourceIsLocalization =
      TraceAnalyticDMgmComparisonSource.isLocalization :=
  rfl

/-- Endpoint localization structure is the stable homotopy comparison
localization structure. -/
theorem TraceAnalyticMotiveComparison.sourceIsLocalization_eq_stableHomotopy :
    TraceAnalyticMotiveComparison.sourceIsLocalization =
      TraceAnalyticStableHomotopyComparisonSource.isLocalization :=
  rfl

/-- Endpoint functor equivalence out of the comparison source. -/
def TraceAnalyticMotiveComparison.sourceFunctorEquivalence
    (target : Type*) [Category target] :
    (TraceAnalyticDMgmComparisonSource ⥤ target) ≌
      TraceAnalyticMotiveComparison.sourceInvertedMorphisms.FunctorsInverting
        target :=
  TraceAnalyticDMgmComparisonSource.functorEquivalence target

/-- Endpoint functor equivalence is the source owner functor equivalence. -/
theorem TraceAnalyticMotiveComparison.sourceFunctorEquivalence_eq_source
    (target : Type*) [Category target] :
    TraceAnalyticMotiveComparison.sourceFunctorEquivalence target =
      TraceAnalyticDMgmComparisonSource.functorEquivalence target :=
  rfl

/-- Endpoint functor equivalence is the stable homotopy comparison functor
equivalence. -/
theorem TraceAnalyticMotiveComparison.sourceFunctorEquivalence_eq_stableHomotopy
    (target : Type*) [Category target] :
    TraceAnalyticMotiveComparison.sourceFunctorEquivalence target =
      TraceAnalyticStableHomotopyComparisonSource.functorEquivalence target :=
  rfl

/-- Endpoint descent of a null-inverting additive homotopy functor to the
comparison source. -/
def TraceAnalyticMotiveComparison.sourceLift
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticMotiveComparison.sourceInvertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticDMgmComparisonSource ⥤ target :=
  TraceAnalyticDMgmComparisonSource.lift functor inverts

/-- Endpoint source lift is the source owner lift. -/
theorem TraceAnalyticMotiveComparison.sourceLift_eq_source
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticMotiveComparison.sourceInvertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.sourceLift functor inverts =
      TraceAnalyticDMgmComparisonSource.lift functor inverts :=
  rfl

/-- Endpoint source lift is the stable homotopy comparison lift. -/
theorem TraceAnalyticMotiveComparison.sourceLift_eq_stableHomotopy
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticMotiveComparison.sourceInvertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.sourceLift functor inverts =
      TraceAnalyticStableHomotopyComparisonSource.lift functor inverts :=
  rfl

/-- Endpoint source lift is the stable analytic localization lift. -/
theorem TraceAnalyticMotiveComparison.sourceLift_eq_stable
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticMotiveComparison.sourceInvertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.sourceLift functor inverts =
      TraceAnalyticStableMotiveCategory.lift functor inverts :=
  TraceAnalyticDMgmComparisonSource.lift_eq_stable
    functor
    inverts

/-- Endpoint descent of a stable homotopy comparison null-inverting additive
homotopy functor to the comparison source. -/
def TraceAnalyticMotiveComparison.stableHomotopySourceLift
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticDMgmComparisonSource ⥤ target :=
  TraceAnalyticStableHomotopyComparisonSource.lift functor inverts

/-- Stable-homotopy endpoint source lift is the stable homotopy comparison
lift. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceLift_eq_stableHomotopy
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.stableHomotopySourceLift functor inverts =
      TraceAnalyticStableHomotopyComparisonSource.lift functor inverts :=
  rfl

/-- Endpoint source lift factorization through the quotient functor. -/
def TraceAnalyticMotiveComparison.sourceLiftFac
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticMotiveComparison.sourceInvertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticDMgmComparisonSource.quotientFunctor ⋙
      TraceAnalyticMotiveComparison.sourceLift functor inverts ≅ functor :=
  TraceAnalyticDMgmComparisonSource.liftFac functor inverts

/-- Endpoint source lift factorization is the source owner factorization. -/
theorem TraceAnalyticMotiveComparison.sourceLiftFac_eq_source
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticMotiveComparison.sourceInvertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.sourceLiftFac functor inverts =
      TraceAnalyticDMgmComparisonSource.liftFac functor inverts :=
  rfl

/-- Endpoint source lift factorization is the stable homotopy comparison
factorization. -/
theorem TraceAnalyticMotiveComparison.sourceLiftFac_eq_stableHomotopy
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticMotiveComparison.sourceInvertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.sourceLiftFac functor inverts =
      TraceAnalyticStableHomotopyComparisonSource.liftFac functor inverts :=
  rfl

/-- Endpoint source lift factorization is the stable analytic localization
factorization. -/
theorem TraceAnalyticMotiveComparison.sourceLiftFac_eq_stable
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticMotiveComparison.sourceInvertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.sourceLiftFac functor inverts =
      TraceAnalyticStableMotiveCategory.liftFac functor inverts :=
  TraceAnalyticDMgmComparisonSource.liftFac_eq_stable
    functor
    inverts

/-- Endpoint factorization for a stable homotopy comparison null-inverting
additive homotopy functor. -/
def TraceAnalyticMotiveComparison.stableHomotopySourceLiftFac
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticDMgmComparisonSource.quotientFunctor ⋙
      TraceAnalyticMotiveComparison.stableHomotopySourceLift functor inverts ≅
        functor :=
  TraceAnalyticStableHomotopyComparisonSource.liftFac functor inverts

/-- Stable-homotopy endpoint source lift factorization is the stable homotopy
comparison factorization. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceLiftFac_eq_stableHomotopy
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticMotiveComparison.stableHomotopySourceLiftFac functor inverts =
      TraceAnalyticStableHomotopyComparisonSource.liftFac functor inverts :=
  rfl

/-- Endpoint lifted natural transformation between stable homotopy comparison
lifts. -/
def TraceAnalyticMotiveComparison.stableHomotopySourceLiftNatTrans
    {target : Type*} [Category target]
    (first second : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (firstLift secondLift : TraceAnalyticStableHomotopyComparisonSource ⥤ target)
    [CategoryTheory.Localization.Lifting
      TraceAnalyticStableHomotopyComparisonSource.quotientFunctor
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
      first
      firstLift]
    [CategoryTheory.Localization.Lifting
      TraceAnalyticStableHomotopyComparisonSource.quotientFunctor
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
      second
      secondLift]
    (transformation : first ⟶ second) :
    firstLift ⟶ secondLift :=
  TraceAnalyticStableHomotopyComparisonSource.liftNatTrans
    first
    second
    firstLift
    secondLift
    transformation

/-- Endpoint lifted natural transformation is the stable homotopy comparison
lifted natural transformation. -/
theorem TraceAnalyticMotiveComparison.stableHomotopySourceLiftNatTrans_eq_stableHomotopy
    {target : Type*} [Category target]
    (first second : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (firstLift secondLift : TraceAnalyticStableHomotopyComparisonSource ⥤ target)
    [CategoryTheory.Localization.Lifting
      TraceAnalyticStableHomotopyComparisonSource.quotientFunctor
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
      first
      firstLift]
    [CategoryTheory.Localization.Lifting
      TraceAnalyticStableHomotopyComparisonSource.quotientFunctor
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
      second
      secondLift]
    (transformation : first ⟶ second) :
    TraceAnalyticMotiveComparison.stableHomotopySourceLiftNatTrans
      first
      second
      firstLift
      secondLift
      transformation =
    TraceAnalyticStableHomotopyComparisonSource.liftNatTrans
      first
      second
      firstLift
      secondLift
      transformation :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
