import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Owner

/-!
# Stable homotopy category evidence for the analytic comparison source

This file collects the comparison-source evidence supplied by the stable
analytic Verdier quotient.  The source used in the comparison is the homotopy
category surface of the analytic stable motive construction: quotient functor,
localization, integer shifts, pretriangulated structure, triangulated structure,
and distinguished triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The stable homotopy comparison source is the analytic comparison source. -/
abbrev TraceAnalyticStableHomotopyComparisonSource :=
  TraceAnalyticDMgmComparisonSource

/-- The stable homotopy comparison source is the stable analytic Verdier
quotient. -/
theorem TraceAnalyticStableHomotopyComparisonSource_eq_stable :
    TraceAnalyticStableHomotopyComparisonSource =
      TraceAnalyticStableMotiveCategory :=
  rfl

/-- The stable homotopy comparison quotient functor is the comparison-source
quotient functor. -/
def TraceAnalyticStableHomotopyComparisonSource.quotientFunctor :
    TraceAnalyticAdditiveHomotopyCategory ⥤
      TraceAnalyticStableHomotopyComparisonSource :=
  TraceAnalyticDMgmComparisonSource.quotientFunctor

/-- The stable homotopy comparison quotient functor is the stable analytic
quotient functor. -/
theorem TraceAnalyticStableHomotopyComparisonSource.quotientFunctor_eq_stable :
    TraceAnalyticStableHomotopyComparisonSource.quotientFunctor =
      TraceAnalyticStableMotiveCategory.quotientFunctor :=
  rfl

/-- The stable homotopy comparison inverted morphisms are the comparison-source
inverted morphisms. -/
def TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms :
    MorphismProperty TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticDMgmComparisonSource.invertedMorphisms

/-- The stable homotopy comparison inverted morphisms are the stable analytic
inverted morphisms. -/
theorem TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms_eq_stable :
    TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms =
      TraceAnalyticStableMotiveCategory.invertedMorphisms :=
  rfl

/-- The stable homotopy comparison source is localized at the stable analytic
inverted morphisms. -/
def TraceAnalyticStableHomotopyComparisonSource.isLocalization :
    TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.IsLocalization
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms :=
  TraceAnalyticDMgmComparisonSource.isLocalization

/-- The stable homotopy comparison localization is the stable analytic
localization. -/
theorem TraceAnalyticStableHomotopyComparisonSource.isLocalization_eq_stable :
    TraceAnalyticStableHomotopyComparisonSource.isLocalization =
      TraceAnalyticStableMotiveCategory.isLocalization :=
  rfl

/-- Additive homotopy objects enter the stable homotopy comparison source
through the stable analytic quotient. -/
def TraceAnalyticStableHomotopyComparisonSource.objectOf
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticStableHomotopyComparisonSource :=
  TraceAnalyticDMgmComparisonSource.objectOf object

/-- The stable homotopy comparison object projection is the stable analytic
object projection. -/
theorem TraceAnalyticStableHomotopyComparisonSource.objectOf_eq_stable
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticStableHomotopyComparisonSource.objectOf object =
      TraceAnalyticStableMotiveCategory.objectOf object :=
  rfl

/-- Additive homotopy morphisms enter the stable homotopy comparison source
through the stable analytic quotient. -/
def TraceAnalyticStableHomotopyComparisonSource.mapOf
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticStableHomotopyComparisonSource.objectOf source ⟶
      TraceAnalyticStableHomotopyComparisonSource.objectOf target :=
  TraceAnalyticDMgmComparisonSource.mapOf hom

/-- The stable homotopy comparison morphism projection is the stable analytic
morphism projection. -/
theorem TraceAnalyticStableHomotopyComparisonSource.mapOf_eq_stable
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticStableHomotopyComparisonSource.mapOf hom =
      TraceAnalyticStableMotiveCategory.mapOf hom :=
  rfl

/-- Functors out of the stable homotopy comparison source are equivalent to
additive homotopy functors that invert stable analytic null morphisms. -/
def TraceAnalyticStableHomotopyComparisonSource.functorEquivalence
    (target : Type*) [Category target] :
    (TraceAnalyticStableHomotopyComparisonSource ⥤ target) ≌
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.FunctorsInverting
        target :=
  TraceAnalyticDMgmComparisonSource.functorEquivalence target

/-- The stable homotopy comparison functor equivalence is the stable analytic
functor equivalence. -/
theorem TraceAnalyticStableHomotopyComparisonSource.functorEquivalence_eq_stable
    (target : Type*) [Category target] :
    TraceAnalyticStableHomotopyComparisonSource.functorEquivalence target =
      TraceAnalyticStableMotiveCategory.functorEquivalence target :=
  rfl

/-- Descend a null-inverting additive homotopy functor to the stable homotopy
comparison source. -/
def TraceAnalyticStableHomotopyComparisonSource.lift
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticStableHomotopyComparisonSource ⥤ target :=
  TraceAnalyticDMgmComparisonSource.lift functor inverts

/-- The stable homotopy comparison lift is the stable analytic lift. -/
theorem TraceAnalyticStableHomotopyComparisonSource.lift_eq_stable
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticStableHomotopyComparisonSource.lift functor inverts =
      TraceAnalyticStableMotiveCategory.lift functor inverts :=
  rfl

/-- The descended stable homotopy comparison functor composed with the quotient
recovers the original additive homotopy functor. -/
def TraceAnalyticStableHomotopyComparisonSource.liftFac
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticStableHomotopyComparisonSource.quotientFunctor ⋙
      TraceAnalyticStableHomotopyComparisonSource.lift functor inverts ≅
        functor :=
  TraceAnalyticDMgmComparisonSource.liftFac functor inverts

/-- The stable homotopy comparison lift factorization is the stable analytic
factorization. -/
theorem TraceAnalyticStableHomotopyComparisonSource.liftFac_eq_stable
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor) :
    TraceAnalyticStableHomotopyComparisonSource.liftFac functor inverts =
      TraceAnalyticStableMotiveCategory.liftFac functor inverts :=
  rfl

/-- Descent across the stable homotopy comparison quotient commutes with
postcomposition of the target functor. -/
def TraceAnalyticStableHomotopyComparisonSource.liftPostcomposeIso
    {target target' : Type*} [Category target] [Category target']
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (post : target ⥤ target') :
    TraceAnalyticStableHomotopyComparisonSource.lift
        (functor ⋙ post)
        (MorphismProperty.IsInvertedBy.of_comp
          TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
          functor
          inverts
          post) ≅
      TraceAnalyticStableHomotopyComparisonSource.lift functor inverts ⋙
        post :=
  CategoryTheory.Localization.liftNatIso
    TraceAnalyticStableHomotopyComparisonSource.quotientFunctor
    TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
    (functor ⋙ post)
    (functor ⋙ post)
    (TraceAnalyticStableHomotopyComparisonSource.lift
      (functor ⋙ post)
      (MorphismProperty.IsInvertedBy.of_comp
        TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
        functor
        inverts
        post))
    (TraceAnalyticStableHomotopyComparisonSource.lift functor inverts ⋙ post)
    (Iso.refl _)

/-- The direct postcomposed lift and the postcomposition of the lift have the
same quotient-factorization source. -/
theorem TraceAnalyticStableHomotopyComparisonSource.liftPostcomposeIso_hom_app_quotient
    {target target' : Type*} [Category target] [Category target']
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (post : target ⥤ target')
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticStableHomotopyComparisonSource.liftPostcomposeIso
      functor
      inverts
      post).hom.app
        (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.obj
          object) =
      (CategoryTheory.Localization.liftNatIso
        TraceAnalyticStableHomotopyComparisonSource.quotientFunctor
        TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
        (functor ⋙ post)
        (functor ⋙ post)
        (TraceAnalyticStableHomotopyComparisonSource.lift
          (functor ⋙ post)
          (MorphismProperty.IsInvertedBy.of_comp
            TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms
            functor
            inverts
            post))
        (TraceAnalyticStableHomotopyComparisonSource.lift functor inverts ⋙
          post)
        (Iso.refl _)).hom.app
        (TraceAnalyticStableHomotopyComparisonSource.quotientFunctor.obj
          object) :=
  rfl

/-- A natural transformation between stable homotopy comparison lifts descends
across the quotient. -/
def TraceAnalyticStableHomotopyComparisonSource.liftNatTrans
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
  TraceAnalyticStableMotiveCategory.liftNatTrans
    first
    second
    firstLift
    secondLift
    transformation

/-- The stable homotopy comparison lifted natural transformation is the stable
analytic lifted natural transformation. -/
theorem TraceAnalyticStableHomotopyComparisonSource.liftNatTrans_eq_stable
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
    TraceAnalyticStableHomotopyComparisonSource.liftNatTrans
      first
      second
      firstLift
      secondLift
      transformation =
    TraceAnalyticStableMotiveCategory.liftNatTrans
      first
      second
      firstLift
      secondLift
      transformation :=
  rfl

/-- The stable homotopy comparison source has the stable analytic shift
structure. -/
def TraceAnalyticStableHomotopyComparisonSource.hasShiftStructure :
    HasShift TraceAnalyticStableHomotopyComparisonSource ℤ :=
  TraceAnalyticDMgmComparisonSource.hasShiftStructure

/-- The stable homotopy comparison shift structure is the stable analytic
shift structure. -/
theorem TraceAnalyticStableHomotopyComparisonSource.hasShiftStructure_eq_stable :
    TraceAnalyticStableHomotopyComparisonSource.hasShiftStructure =
      TraceAnalyticStableMotiveCategory.hasShiftStructure :=
  rfl

/-- The stable homotopy comparison source has the stable analytic
pretriangulated structure. -/
def TraceAnalyticStableHomotopyComparisonSource.pretriangulatedStructure :
    Pretriangulated TraceAnalyticStableHomotopyComparisonSource :=
  TraceAnalyticDMgmComparisonSource.pretriangulatedStructure

/-- The stable homotopy comparison pretriangulated structure is the stable
analytic pretriangulated structure. -/
theorem TraceAnalyticStableHomotopyComparisonSource.pretriangulatedStructure_eq_stable :
    TraceAnalyticStableHomotopyComparisonSource.pretriangulatedStructure =
      TraceAnalyticStableMotiveCategory.pretriangulatedStructure :=
  rfl

/-- The stable homotopy comparison source has the stable analytic triangulated
structure. -/
def TraceAnalyticStableHomotopyComparisonSource.triangulatedStructure :
    IsTriangulated TraceAnalyticStableHomotopyComparisonSource :=
  TraceAnalyticDMgmComparisonSource.triangulatedStructure

/-- The stable homotopy comparison triangulated structure is the stable
analytic triangulated structure. -/
theorem TraceAnalyticStableHomotopyComparisonSource.triangulatedStructure_eq_stable :
    TraceAnalyticStableHomotopyComparisonSource.triangulatedStructure =
      TraceAnalyticStableMotiveCategory.triangulatedStructure :=
  rfl

/-- The stable homotopy comparison distinguished triangles are the stable
analytic distinguished triangles. -/
def TraceAnalyticStableHomotopyComparisonSource.distinguishedTriangles :
    Set (Pretriangulated.Triangle
      TraceAnalyticStableHomotopyComparisonSource) :=
  TraceAnalyticDMgmComparisonSource.distinguishedTriangles

/-- The stable homotopy comparison distinguished triangles are the stable
analytic distinguished triangles. -/
theorem TraceAnalyticStableHomotopyComparisonSource.distinguishedTriangles_eq_stable :
    TraceAnalyticStableHomotopyComparisonSource.distinguishedTriangles =
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
