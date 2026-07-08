import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.CompactInterpretation.Composition.Owner

/-!
# Forward compact interpretations for composable input pairs

This file names the two forward compact interpretations attached to a
composable pair.  The left interpretation is already typed from the pair
source to the pair middle.  The right interpretation is intentionally recorded
before endpoint transport, because its source is the right input source
generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left forward compact interpretation of a composable pair. -/
def TraceLocalizationInputComposablePair.leftForward
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceGenerator ⟶ pair.middleGenerator :=
  pair.left.unstableForwardCompactInterpretation

/-- The right forward compact interpretation before transporting across the middle equality. -/
def TraceLocalizationInputComposablePair.rightForwardBeforeTransport
    (pair : TraceLocalizationInputComposablePair) :
    pair.right.sourceGenerator ⟶ pair.targetGenerator :=
  pair.right.unstableForwardCompactInterpretation

/-- The right forward compact interpretation transported across the certified middle endpoint. -/
def TraceLocalizationInputComposablePair.rightForward
    (pair : TraceLocalizationInputComposablePair) :
    pair.middleGenerator ⟶ pair.targetGenerator :=
  match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
  | rfl => pair.rightForwardBeforeTransport

/-- The composed forward compact interpretation of a composable pair. -/
def TraceLocalizationInputComposablePair.composedForward
    (pair : TraceLocalizationInputComposablePair) :
    pair.sourceGenerator ⟶ pair.targetGenerator :=
  pair.leftForward ≫ pair.rightForward

/-- The left forward interpretation is the left input forward compact interpretation. -/
theorem TraceLocalizationInputComposablePair.leftForward_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward =
      pair.left.unstableForwardCompactInterpretation :=
  rfl

/-- The right forward interpretation before transport is the right input forward interpretation. -/
theorem TraceLocalizationInputComposablePair.rightForwardBeforeTransport_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport =
      pair.right.unstableForwardCompactInterpretation :=
  rfl

/-- The transported right forward interpretation is transported from the right input arrow. -/
theorem TraceLocalizationInputComposablePair.rightForward_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.rightForwardBeforeTransport :=
  rfl

/-- The composed forward interpretation is the left forward map followed by the transported right map. -/
theorem TraceLocalizationInputComposablePair.composedForward_eq_comp
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward =
      pair.leftForward ≫ pair.rightForward :=
  rfl

/-- Left identity for the composed forward interpretation of a composable pair. -/
theorem TraceLocalizationInputComposablePair.id_comp_composedForward
    (pair : TraceLocalizationInputComposablePair) :
    (𝟙 pair.sourceGenerator : pair.sourceGenerator ⟶ pair.sourceGenerator) ≫
        pair.composedForward =
      pair.composedForward :=
  TraceCorQHom.left_id
    pair.composedForward

/-- Right identity for the composed forward interpretation of a composable pair. -/
theorem TraceLocalizationInputComposablePair.composedForward_comp_id
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward ≫
        (𝟙 pair.targetGenerator : pair.targetGenerator ⟶ pair.targetGenerator) =
      pair.composedForward :=
  TraceCorQHom.right_id
    pair.composedForward

/-- The left forward interpretation has the left input trace hom. -/
theorem TraceLocalizationInputComposablePair.leftForward_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward.traceHom =
      pair.left.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_traceHom
    pair.left

/-- The right forward interpretation before transport has the right input trace hom. -/
theorem TraceLocalizationInputComposablePair.rightForwardBeforeTransport_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport.traceHom =
      pair.right.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_traceHom
    pair.right

/-- The composed forward interpretation has composite trace hom. -/
theorem TraceLocalizationInputComposablePair.composedForward_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.traceHom =
      pair.leftForward.traceHom ≫ pair.rightForward.traceHom :=
  TraceAnalyticGeometricGenerator.comp_traceHom
    pair.leftForward
    pair.rightForward

/-- The composed forward interpretation has the left input trace hom in its first factor. -/
theorem TraceLocalizationInputComposablePair.composedForward_traceHom_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.traceHom =
      pair.left.traceHom ≫ pair.rightForward.traceHom :=
  Eq.trans
    (TraceLocalizationInputComposablePair.composedForward_traceHom pair)
    (congrArg
      (fun traceHom =>
        traceHom ≫ pair.rightForward.traceHom)
      (TraceLocalizationInputComposablePair.leftForward_traceHom pair))

/-- Left identity for the trace hom of the composed forward interpretation. -/
theorem TraceLocalizationInputComposablePair.id_comp_composedForward_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    ((𝟙 pair.sourceGenerator : pair.sourceGenerator ⟶ pair.sourceGenerator) ≫
        pair.composedForward).traceHom =
      pair.composedForward.traceHom :=
  congrArg
    (fun morphism =>
      morphism.traceHom)
    (TraceLocalizationInputComposablePair.id_comp_composedForward pair)

/-- Right identity for the trace hom of the composed forward interpretation. -/
theorem TraceLocalizationInputComposablePair.composedForward_comp_id_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (pair.composedForward ≫
        (𝟙 pair.targetGenerator : pair.targetGenerator ⟶ pair.targetGenerator)).traceHom =
      pair.composedForward.traceHom :=
  congrArg
    (fun morphism =>
      morphism.traceHom)
    (TraceLocalizationInputComposablePair.composedForward_comp_id pair)

/-- The left forward interpretation induces the left input presheaf map. -/
theorem TraceLocalizationInputComposablePair.leftForward_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward.representableMap =
      pair.left.map :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_representableMap
    pair.left

/-- The right forward interpretation before transport induces the right input presheaf map. -/
theorem TraceLocalizationInputComposablePair.rightForwardBeforeTransport_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport.representableMap =
      pair.right.map :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_representableMap
    pair.right

/-- The composed forward interpretation has composite representable map. -/
theorem TraceLocalizationInputComposablePair.composedForward_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.representableMap =
      pair.leftForward.representableMap ≫ pair.rightForward.representableMap :=
  TraceAnalyticGeometricGenerator.comp_representableMap
    pair.leftForward
    pair.rightForward

/-- The composed forward interpretation has the left input map in its first presheaf factor. -/
theorem TraceLocalizationInputComposablePair.composedForward_representableMap_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.representableMap =
      pair.left.map ≫ pair.rightForward.representableMap :=
  Eq.trans
    (TraceLocalizationInputComposablePair.composedForward_representableMap pair)
    (congrArg
      (fun map =>
        map ≫ pair.rightForward.representableMap)
      (TraceLocalizationInputComposablePair.leftForward_representableMap pair))

/-- Left identity for the representable map of the composed forward interpretation. -/
theorem TraceLocalizationInputComposablePair.id_comp_composedForward_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    ((𝟙 pair.sourceGenerator : pair.sourceGenerator ⟶ pair.sourceGenerator) ≫
        pair.composedForward).representableMap =
      pair.composedForward.representableMap :=
  congrArg
    (fun morphism =>
      morphism.representableMap)
    (TraceLocalizationInputComposablePair.id_comp_composedForward pair)

/-- Right identity for the representable map of the composed forward interpretation. -/
theorem TraceLocalizationInputComposablePair.composedForward_comp_id_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    (pair.composedForward ≫
        (𝟙 pair.targetGenerator : pair.targetGenerator ⟶ pair.targetGenerator)).representableMap =
      pair.composedForward.representableMap :=
  congrArg
    (fun morphism =>
      morphism.representableMap)
    (TraceLocalizationInputComposablePair.composedForward_comp_id pair)

/-- The compact presheaf functor sends the left forward interpretation to the left input map. -/
theorem TraceLocalizationInputComposablePair.leftForward_presheafFunctor_map
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map pair.leftForward =
      pair.left.map :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_presheafFunctor_map
    pair.left

/-- The compact presheaf functor sends the right forward-before-transport map to the right input map. -/
theorem TraceLocalizationInputComposablePair.rightForwardBeforeTransport_presheafFunctor_map
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map
        pair.rightForwardBeforeTransport =
      pair.right.map :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_presheafFunctor_map
    pair.right

/-- The lifted left forward map is the Yoneda map of the left input trace hom. -/
theorem TraceLocalizationInputComposablePair.leftForward_representableObjectMap_eq_yoneda
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map pair.left.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_representableObjectMap_eq_yoneda
    pair.left

/-- The lifted right forward-before-transport map is the Yoneda map of the right input trace hom. -/
theorem TraceLocalizationInputComposablePair.rightForwardBeforeTransport_representableObjectMap_eq_yoneda
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map pair.right.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_representableObjectMap_eq_yoneda
    pair.right

/-- Including the lifted left forward map recovers the left input map. -/
theorem TraceLocalizationInputComposablePair.leftForward_representableObjectMap_inclusion
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQRepresentablePresheaf.inclusion.map
        pair.leftForward.representableObjectMap =
      pair.left.map :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_representableObjectMap_inclusion
    pair.left

/-- Including the lifted right forward-before-transport map recovers the right input map. -/
theorem TraceLocalizationInputComposablePair.rightForwardBeforeTransport_representableObjectMap_inclusion
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQRepresentablePresheaf.inclusion.map
        pair.rightForwardBeforeTransport.representableObjectMap =
      pair.right.map :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_representableObjectMap_inclusion
    pair.right

/-- Scalar multiplication of the left forward interpretation is trace scalar multiplication. -/
theorem TraceLocalizationInputComposablePair.leftForward_smul_traceHom
    (pair : TraceLocalizationInputComposablePair)
    (coefficient : Rat) :
    (coefficient • pair.leftForward).traceHom =
      coefficient • pair.left.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_smul_traceHom
    pair.left
    coefficient

/-- Scalar multiplication of the right forward-before-transport map is trace scalar multiplication. -/
theorem TraceLocalizationInputComposablePair.rightForwardBeforeTransport_smul_traceHom
    (pair : TraceLocalizationInputComposablePair)
    (coefficient : Rat) :
    (coefficient • pair.rightForwardBeforeTransport).traceHom =
      coefficient • pair.right.traceHom :=
  TraceLocalizationInput.unstableForwardCompactInterpretation_smul_traceHom
    pair.right
    coefficient

/-- The zero compact morphism on the left pair segment has zero trace hom. -/
theorem TraceLocalizationInputComposablePair.leftZero_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (0 : pair.sourceGenerator ⟶ pair.middleGenerator).traceHom =
      (0 : pair.sourceObject ⟶ pair.middleObject) :=
  TraceAnalyticGeometricGenerator.zero_traceHom

/-- The zero compact morphism on the right-before-transport segment has zero trace hom. -/
theorem TraceLocalizationInputComposablePair.rightZeroBeforeTransport_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (0 : pair.right.sourceGenerator ⟶ pair.targetGenerator).traceHom =
      (0 : pair.right.sourceObject ⟶ pair.targetObject) :=
  TraceAnalyticGeometricGenerator.zero_traceHom

/-- Negating the left forward interpretation negates its trace hom. -/
theorem TraceLocalizationInputComposablePair.leftForward_traceNeg_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (TraceCorQHom.neg pair.leftForward).traceHom =
      TraceCorQHom.neg pair.left.traceHom :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.traceNeg_traceHom
      pair.leftForward)
    (congrArg
      TraceCorQHom.neg
      (TraceLocalizationInputComposablePair.leftForward_traceHom pair))

/-- Negating the right forward-before-transport map negates its trace hom. -/
theorem TraceLocalizationInputComposablePair.rightForwardBeforeTransport_traceNeg_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (TraceCorQHom.neg pair.rightForwardBeforeTransport).traceHom =
      TraceCorQHom.neg pair.right.traceHom :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.traceNeg_traceHom
      pair.rightForwardBeforeTransport)
    (congrArg
      TraceCorQHom.neg
      (TraceLocalizationInputComposablePair.rightForwardBeforeTransport_traceHom pair))

/-- Subtracting the left forward interpretation from itself gives zero. -/
theorem TraceLocalizationInputComposablePair.leftForward_traceSub_self
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQHom.sub pair.leftForward pair.leftForward =
      TraceCorQHom.zero pair.sourceObject pair.middleObject :=
  TraceAnalyticGeometricGenerator.traceSub_self_traceHom
    pair.leftForward

/-- Subtracting the right forward-before-transport map from itself gives zero. -/
theorem TraceLocalizationInputComposablePair.rightForwardBeforeTransport_traceSub_self
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQHom.sub
        pair.rightForwardBeforeTransport
        pair.rightForwardBeforeTransport =
      TraceCorQHom.zero pair.right.sourceObject pair.targetObject :=
  TraceAnalyticGeometricGenerator.traceSub_self_traceHom
    pair.rightForwardBeforeTransport

/-- Scalar multiplication distributes over self-subtraction of the left forward interpretation. -/
theorem TraceLocalizationInputComposablePair.leftForward_traceSmul_sub_self
    (pair : TraceLocalizationInputComposablePair)
    (coefficient : Rat) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub pair.leftForward pair.leftForward) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient pair.leftForward)
        (TraceCorQHom.smul coefficient pair.leftForward) :=
  TraceAnalyticGeometricGenerator.traceSmul_sub
    coefficient
    pair.leftForward
    pair.leftForward

/-- Scalar multiplication distributes over self-subtraction of the right forward-before-transport map. -/
theorem TraceLocalizationInputComposablePair.rightForwardBeforeTransport_traceSmul_sub_self
    (pair : TraceLocalizationInputComposablePair)
    (coefficient : Rat) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub
        pair.rightForwardBeforeTransport
        pair.rightForwardBeforeTransport) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient pair.rightForwardBeforeTransport)
        (TraceCorQHom.smul coefficient pair.rightForwardBeforeTransport) :=
  TraceAnalyticGeometricGenerator.traceSmul_sub
    coefficient
    pair.rightForwardBeforeTransport
    pair.rightForwardBeforeTransport

end AnalyticMotives
end LFunctions
end Boundary
