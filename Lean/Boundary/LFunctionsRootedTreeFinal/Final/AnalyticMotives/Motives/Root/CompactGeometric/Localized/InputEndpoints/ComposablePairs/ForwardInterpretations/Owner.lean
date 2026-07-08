import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.Owner

/-!
# Motive-root forward interpretations for composable input pairs

This file exposes the forward compact interpretations attached to composable
localization-input pairs through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: the left forward interpretation is the left input forward interpretation. -/
theorem TraceAnalyticMotive.composablePair_leftForward_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward =
      pair.left.unstableForwardCompactInterpretation :=
  TraceLocalizationInputComposablePair.leftForward_eq_left
    pair

/-- Motive-root wrapper: the right forward-before-transport map is the right input forward interpretation. -/
theorem TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport =
      pair.right.unstableForwardCompactInterpretation :=
  TraceLocalizationInputComposablePair.rightForwardBeforeTransport_eq_right
    pair

/-- Motive-root wrapper: the transported right forward map is transported across the middle endpoint. -/
theorem TraceAnalyticMotive.composablePair_rightForward_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.rightForwardBeforeTransport :=
  TraceLocalizationInputComposablePair.rightForward_eq_transport
    pair

/-- Motive-root wrapper: the composed forward map is left forward followed by transported right. -/
theorem TraceAnalyticMotive.composablePair_composedForward_eq_comp
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward =
      pair.leftForward ≫ pair.rightForward :=
  TraceLocalizationInputComposablePair.composedForward_eq_comp
    pair

/-- Motive-root wrapper: left identity for the composed forward interpretation. -/
theorem TraceAnalyticMotive.composablePair_id_comp_composedForward
    (pair : TraceLocalizationInputComposablePair) :
    (𝟙 pair.sourceGenerator : pair.sourceGenerator ⟶ pair.sourceGenerator) ≫
        pair.composedForward =
      pair.composedForward :=
  TraceLocalizationInputComposablePair.id_comp_composedForward
    pair

/-- Motive-root wrapper: right identity for the composed forward interpretation. -/
theorem TraceAnalyticMotive.composablePair_composedForward_comp_id
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward ≫
        (𝟙 pair.targetGenerator : pair.targetGenerator ⟶ pair.targetGenerator) =
      pair.composedForward :=
  TraceLocalizationInputComposablePair.composedForward_comp_id
    pair

/-- Motive-root wrapper: the left forward interpretation has the left trace hom. -/
theorem TraceAnalyticMotive.composablePair_leftForward_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward.traceHom =
      pair.left.traceHom :=
  TraceLocalizationInputComposablePair.leftForward_traceHom
    pair

/-- Motive-root wrapper: the right forward-before-transport map has the right trace hom. -/
theorem TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport.traceHom =
      pair.right.traceHom :=
  TraceLocalizationInputComposablePair.rightForwardBeforeTransport_traceHom
    pair

/-- Motive-root wrapper: the composed forward map has composite trace hom. -/
theorem TraceAnalyticMotive.composablePair_composedForward_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.traceHom =
      pair.leftForward.traceHom ≫ pair.rightForward.traceHom :=
  TraceLocalizationInputComposablePair.composedForward_traceHom
    pair

/-- Motive-root wrapper: the composed forward trace hom has the left input trace hom first. -/
theorem TraceAnalyticMotive.composablePair_composedForward_traceHom_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.traceHom =
      pair.left.traceHom ≫ pair.rightForward.traceHom :=
  TraceLocalizationInputComposablePair.composedForward_traceHom_left
    pair

/-- Motive-root wrapper: left identity for the trace hom of the composed forward map. -/
theorem TraceAnalyticMotive.composablePair_id_comp_composedForward_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    ((𝟙 pair.sourceGenerator : pair.sourceGenerator ⟶ pair.sourceGenerator) ≫
        pair.composedForward).traceHom =
      pair.composedForward.traceHom :=
  TraceLocalizationInputComposablePair.id_comp_composedForward_traceHom
    pair

/-- Motive-root wrapper: right identity for the trace hom of the composed forward map. -/
theorem TraceAnalyticMotive.composablePair_composedForward_comp_id_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (pair.composedForward ≫
        (𝟙 pair.targetGenerator : pair.targetGenerator ⟶ pair.targetGenerator)).traceHom =
      pair.composedForward.traceHom :=
  TraceLocalizationInputComposablePair.composedForward_comp_id_traceHom
    pair

/-- Motive-root wrapper: the left forward interpretation induces the left input map. -/
theorem TraceAnalyticMotive.composablePair_leftForward_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward.representableMap =
      pair.left.map :=
  TraceLocalizationInputComposablePair.leftForward_representableMap
    pair

/-- Motive-root wrapper: the right forward-before-transport map induces the right input map. -/
theorem TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport.representableMap =
      pair.right.map :=
  TraceLocalizationInputComposablePair.rightForwardBeforeTransport_representableMap
    pair

/-- Motive-root wrapper: the composed forward map has composite representable map. -/
theorem TraceAnalyticMotive.composablePair_composedForward_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.representableMap =
      pair.leftForward.representableMap ≫ pair.rightForward.representableMap :=
  TraceLocalizationInputComposablePair.composedForward_representableMap
    pair

/-- Motive-root wrapper: the composed forward representable map has the left input map first. -/
theorem TraceAnalyticMotive.composablePair_composedForward_representableMap_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.representableMap =
      pair.left.map ≫ pair.rightForward.representableMap :=
  TraceLocalizationInputComposablePair.composedForward_representableMap_left
    pair

/-- Motive-root wrapper: left identity for the representable map of the composed forward map. -/
theorem TraceAnalyticMotive.composablePair_id_comp_composedForward_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    ((𝟙 pair.sourceGenerator : pair.sourceGenerator ⟶ pair.sourceGenerator) ≫
        pair.composedForward).representableMap =
      pair.composedForward.representableMap :=
  TraceLocalizationInputComposablePair.id_comp_composedForward_representableMap
    pair

/-- Motive-root wrapper: right identity for the representable map of the composed forward map. -/
theorem TraceAnalyticMotive.composablePair_composedForward_comp_id_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    (pair.composedForward ≫
        (𝟙 pair.targetGenerator : pair.targetGenerator ⟶ pair.targetGenerator)).representableMap =
      pair.composedForward.representableMap :=
  TraceLocalizationInputComposablePair.composedForward_comp_id_representableMap
    pair

/-- Motive-root wrapper: the presheaf functor sends the left forward map to the left input map. -/
theorem TraceAnalyticMotive.composablePair_leftForward_presheafFunctor_map
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map pair.leftForward =
      pair.left.map :=
  TraceLocalizationInputComposablePair.leftForward_presheafFunctor_map
    pair

/-- Motive-root wrapper: the presheaf functor sends the right forward-before-transport map to the right input map. -/
theorem TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_presheafFunctor_map
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map
        pair.rightForwardBeforeTransport =
      pair.right.map :=
  TraceLocalizationInputComposablePair.rightForwardBeforeTransport_presheafFunctor_map
    pair

/-- Motive-root wrapper: the lifted left forward map is the Yoneda map of the left trace hom. -/
theorem TraceAnalyticMotive.composablePair_leftForward_representableObjectMap_eq_yoneda
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map pair.left.traceHom :=
  TraceLocalizationInputComposablePair.leftForward_representableObjectMap_eq_yoneda
    pair

/-- Motive-root wrapper: the lifted right forward-before-transport map is the Yoneda map of the right trace hom. -/
theorem TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_representableObjectMap_eq_yoneda
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map pair.right.traceHom :=
  TraceLocalizationInputComposablePair.rightForwardBeforeTransport_representableObjectMap_eq_yoneda
    pair

/-- Motive-root wrapper: including the lifted left forward map recovers the left input map. -/
theorem TraceAnalyticMotive.composablePair_leftForward_representableObjectMap_inclusion
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQRepresentablePresheaf.inclusion.map
        pair.leftForward.representableObjectMap =
      pair.left.map :=
  TraceLocalizationInputComposablePair.leftForward_representableObjectMap_inclusion
    pair

/-- Motive-root wrapper: including the lifted right forward-before-transport map recovers the right input map. -/
theorem TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_representableObjectMap_inclusion
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQRepresentablePresheaf.inclusion.map
        pair.rightForwardBeforeTransport.representableObjectMap =
      pair.right.map :=
  TraceLocalizationInputComposablePair.rightForwardBeforeTransport_representableObjectMap_inclusion
    pair

/-- Motive-root wrapper: scalar multiplication of the left forward interpretation is trace scalar multiplication. -/
theorem TraceAnalyticMotive.composablePair_leftForward_smul_traceHom
    (pair : TraceLocalizationInputComposablePair)
    (coefficient : Rat) :
    (coefficient • pair.leftForward).traceHom =
      coefficient • pair.left.traceHom :=
  TraceLocalizationInputComposablePair.leftForward_smul_traceHom
    pair
    coefficient

/-- Motive-root wrapper: scalar multiplication of the right forward-before-transport map is trace scalar multiplication. -/
theorem TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_smul_traceHom
    (pair : TraceLocalizationInputComposablePair)
    (coefficient : Rat) :
    (coefficient • pair.rightForwardBeforeTransport).traceHom =
      coefficient • pair.right.traceHom :=
  TraceLocalizationInputComposablePair.rightForwardBeforeTransport_smul_traceHom
    pair
    coefficient

/-- Motive-root wrapper: the zero compact morphism on the left pair segment has zero trace hom. -/
theorem TraceAnalyticMotive.composablePair_leftZero_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (0 : pair.sourceGenerator ⟶ pair.middleGenerator).traceHom =
      (0 : pair.sourceObject ⟶ pair.middleObject) :=
  TraceLocalizationInputComposablePair.leftZero_traceHom
    pair

/-- Motive-root wrapper: the zero compact morphism on the right-before-transport segment has zero trace hom. -/
theorem TraceAnalyticMotive.composablePair_rightZeroBeforeTransport_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (0 : pair.right.sourceGenerator ⟶ pair.targetGenerator).traceHom =
      (0 : pair.right.sourceObject ⟶ pair.targetObject) :=
  TraceLocalizationInputComposablePair.rightZeroBeforeTransport_traceHom
    pair

/-- Motive-root wrapper: negating the left forward interpretation negates its trace hom. -/
theorem TraceAnalyticMotive.composablePair_leftForward_traceNeg_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (TraceCorQHom.neg pair.leftForward).traceHom =
      TraceCorQHom.neg pair.left.traceHom :=
  TraceLocalizationInputComposablePair.leftForward_traceNeg_traceHom
    pair

/-- Motive-root wrapper: negating the right forward-before-transport map negates its trace hom. -/
theorem TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_traceNeg_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (TraceCorQHom.neg pair.rightForwardBeforeTransport).traceHom =
      TraceCorQHom.neg pair.right.traceHom :=
  TraceLocalizationInputComposablePair.rightForwardBeforeTransport_traceNeg_traceHom
    pair

/-- Motive-root wrapper: subtracting the left forward interpretation from itself gives zero. -/
theorem TraceAnalyticMotive.composablePair_leftForward_traceSub_self
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQHom.sub pair.leftForward pair.leftForward =
      TraceCorQHom.zero pair.sourceObject pair.middleObject :=
  TraceLocalizationInputComposablePair.leftForward_traceSub_self
    pair

/-- Motive-root wrapper: subtracting the right forward-before-transport map from itself gives zero. -/
theorem TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_traceSub_self
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQHom.sub
        pair.rightForwardBeforeTransport
        pair.rightForwardBeforeTransport =
      TraceCorQHom.zero pair.right.sourceObject pair.targetObject :=
  TraceLocalizationInputComposablePair.rightForwardBeforeTransport_traceSub_self
    pair

/-- Motive-root wrapper: scalar multiplication distributes over self-subtraction of the left forward interpretation. -/
theorem TraceAnalyticMotive.composablePair_leftForward_traceSmul_sub_self
    (pair : TraceLocalizationInputComposablePair)
    (coefficient : Rat) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub pair.leftForward pair.leftForward) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient pair.leftForward)
        (TraceCorQHom.smul coefficient pair.leftForward) :=
  TraceLocalizationInputComposablePair.leftForward_traceSmul_sub_self
    pair
    coefficient

/-- Motive-root wrapper: scalar multiplication distributes over self-subtraction of the right forward-before-transport map. -/
theorem TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_traceSmul_sub_self
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
  TraceLocalizationInputComposablePair.rightForwardBeforeTransport_traceSmul_sub_self
    pair
    coefficient

end AnalyticMotives
end LFunctions
end Boundary
