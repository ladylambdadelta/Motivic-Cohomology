import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.TateStabilization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Rotation.ShortComplex.Owner

/-!
# Motive-root Tate rotated short complexes

This file exposes the rotated and inverse-rotated short complexes of the Tate
weight-drop bounded mapping cone through the motive-root namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root facade: the rotated short complex of the Tate bounded mapping cone. -/
def TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeRotatedShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex

/-- Motive-root facade: the inverse-rotated short complex of the Tate bounded mapping
cone. -/
def TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeInverseRotatedShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex

/-- Motive-root facade: the Tate rotated short complex has the target object as its
left vertex. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeRotatedShortComplex_X₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_X₁
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate rotated short complex has the cone object as its middle
vertex. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeRotatedShortComplex_X₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_X₂
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate rotated short complex has the shifted source object as
its right vertex. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeRotatedShortComplex_X₃
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.X₃ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom)⟦(1 : ℤ)⟧ :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_X₃
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the first morphism of the Tate rotated short complex is cone
inclusion. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeRotatedShortComplex_f
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_f
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the second morphism of the Tate rotated short complex is the
connecting map. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeRotatedShortComplex_g
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_g
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate rotated short complex has zero composite. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeRotatedShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.f ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedShortComplex_zero
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate inverse-rotated short complex has the shifted cone
object as its left vertex. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeInverseRotatedShortComplex_X₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.X₁ =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧ :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_X₁
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate inverse-rotated short complex has the source object as
its middle vertex. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeInverseRotatedShortComplex_X₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_X₂
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate inverse-rotated short complex has the target object as
its right vertex. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeInverseRotatedShortComplex_X₃
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_X₃
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the first morphism of the Tate inverse-rotated short complex is
the shifted negative connecting map with unit transport. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeInverseRotatedShortComplex_f
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.f =
      -(TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom)⟦(-1 : ℤ)⟧' ≫
        (shiftEquiv TraceAnalyticAdditiveHomotopyCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_f
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the second morphism of the Tate inverse-rotated short complex is
the bounded map. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeInverseRotatedShortComplex_g
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_g
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Motive-root facade: the Tate inverse-rotated short complex has zero composite. -/
theorem TraceAnalyticMotive.rootTateStabilization_weightDrop_boundedMappingConeInverseRotatedShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.f ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedShortComplex.g =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedShortComplex_zero
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
