import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmFunctor.HomotopyRestriction.TraceObjects.Owner

/-!
# Additive-object restriction of homotopy-level recognition functors

This file records the concrete finite-family restriction obtained by embedding
an additive trace family as a degree-zero complex and then applying the supplied
homotopy-level Boundary-DMgm functor.
-/

universe u

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- The additive finite-family restriction of a homotopy-level recognition
functor. -/
def TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    TraceAnalyticAdditiveCategoryObject ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject (0 : ℤ) ⋙
    TraceAnalyticAdditiveHomotopyCategory.quotientFunctor ⋙
      homotopyFunctor

/-- The additive-object restriction is the degree-zero complex embedding
followed by the homotopy quotient and the supplied homotopy-level functor. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_eq_comp
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition)) :
    TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor =
      CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
          (0 : ℤ) ⋙
        TraceAnalyticAdditiveHomotopyCategory.quotientFunctor ⋙
          homotopyFunctor :=
  rfl

/-- Object formula for the additive finite-family restriction. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_obj
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (object : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).obj object =
      homotopyFunctor.obj
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          ((CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
            (0 : ℤ)).obj object)) :=
  rfl

/-- Map formula for the additive finite-family restriction. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_map
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map hom =
      homotopyFunctor.map
        (TraceAnalyticAdditiveHomotopyCategory.mapOf
          ((CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
            (0 : ℤ)).map hom)) :=
  rfl

/-- On singleton additive objects, the additive finite-family restriction
recovers the trace-object restriction. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_obj_singleton
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (object : TraceCorQObject) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).obj
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveObject object) =
      (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).obj object :=
  rfl

/-- On singleton trace matrices, the additive finite-family restriction
recovers the trace-object restriction. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_map_singleton
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    {source target : TraceCorQObject}
    (hom : source ⟶ target) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceAnalyticMotiveComparison.sourceTraceAdditiveMap hom) =
      (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map hom :=
  rfl

/-- The additive finite-family restriction sends a rewrite generator's additive
stage to the same target map as its trace-object restriction. -/
theorem TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor_rewriteGeneratorMap
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (generator : TraceRewriteGenerator) :
    (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          generator) =
      (TraceAnalyticMotiveRecognition.traceObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).map generator.traceHom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
