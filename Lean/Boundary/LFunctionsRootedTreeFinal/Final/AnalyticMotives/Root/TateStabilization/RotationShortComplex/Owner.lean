import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.TateStabilization.RotationShortComplex.Owner

/-!
# Public Tate rotated short-complex facade

This file exposes Tate rotated and inverse-rotated bounded mapping-cone
short-complex projections at the top root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public root summary: the rotated short complex of the Tate bounded mapping cone. -/
def AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedShortComplex
    source
    target

/-- Public root summary: the inverse-rotated short complex of the Tate bounded mapping
cone. -/
def AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex
    source
    target

/-- Public root summary: the Tate rotated short complex has the target object as its left
vertex. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedShortComplex_X₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedShortComplex_X₁
    source
    target

/-- Public root summary: the Tate rotated short complex has the cone object as its middle
vertex. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedShortComplex_X₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedShortComplex_X₂
    source
    target

/-- Public root summary: the Tate rotated short complex has the shifted source object as
its right vertex. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedShortComplex_X₃
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.X₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom)⟦(1 : ℤ)⟧ :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedShortComplex_X₃
    source
    target

/-- Public root summary: the first morphism of the Tate rotated short complex is cone
inclusion. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedShortComplex_f
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedShortComplex_f
    source
    target

/-- Public root summary: the second morphism of the Tate rotated short complex is the
connecting map. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedShortComplex_g
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedShortComplex_g
    source
    target

/-- Public root summary: the Tate rotated short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.f ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedShortComplex_zero
    source
    target

/-- Public root summary: the Tate inverse-rotated short complex has the shifted cone
object as its left vertex. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_X₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.X₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧ :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_X₁
    source
    target

/-- Public root summary: the Tate inverse-rotated short complex has the source object as
its middle vertex. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_X₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_X₂
    source
    target

/-- Public root summary: the Tate inverse-rotated short complex has the target object as
its right vertex. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_X₃
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_X₃
    source
    target

/-- Public root summary: the first morphism of the Tate inverse-rotated short complex is
the shifted negative connecting map with unit transport. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_f
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.f =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_f
    source
    target

/-- Public root summary: the second morphism of the Tate inverse-rotated short complex
is the bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_g
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_g
    source
    target

/-- Public root summary: the Tate inverse-rotated short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.f ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedShortComplex_zero
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
