import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ForwardInterpretations.Owner

/-!
# Public forward interpretations for composable input pairs

This file exposes the forward compact interpretations attached to composable
localization-input pairs through the public analytic-motives root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: the left forward interpretation is the left input forward interpretation. -/
theorem AnalyticMotivesRoot.composablePair_leftForward_eq_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward =
      pair.left.unstableForwardCompactInterpretation :=
  TraceAnalyticMotive.composablePair_leftForward_eq_left
    pair

/-- Public wrapper: the right forward-before-transport map is the right input forward interpretation. -/
theorem AnalyticMotivesRoot.composablePair_rightForwardBeforeTransport_eq_right
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport =
      pair.right.unstableForwardCompactInterpretation :=
  TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_eq_right
    pair

/-- Public wrapper: the transported right forward map is transported across the middle endpoint. -/
theorem AnalyticMotivesRoot.composablePair_rightForward_eq_transport
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForward =
      match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source pair with
      | rfl => pair.rightForwardBeforeTransport :=
  TraceAnalyticMotive.composablePair_rightForward_eq_transport
    pair

/-- Public wrapper: the composed forward map is left forward followed by transported right. -/
theorem AnalyticMotivesRoot.composablePair_composedForward_eq_comp
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward =
      pair.leftForward ≫ pair.rightForward :=
  TraceAnalyticMotive.composablePair_composedForward_eq_comp
    pair

/-- Public wrapper: left identity for the composed forward interpretation. -/
theorem AnalyticMotivesRoot.composablePair_id_comp_composedForward
    (pair : TraceLocalizationInputComposablePair) :
    (𝟙 pair.sourceGenerator : pair.sourceGenerator ⟶ pair.sourceGenerator) ≫
        pair.composedForward =
      pair.composedForward :=
  TraceAnalyticMotive.composablePair_id_comp_composedForward
    pair

/-- Public wrapper: right identity for the composed forward interpretation. -/
theorem AnalyticMotivesRoot.composablePair_composedForward_comp_id
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward ≫
        (𝟙 pair.targetGenerator : pair.targetGenerator ⟶ pair.targetGenerator) =
      pair.composedForward :=
  TraceAnalyticMotive.composablePair_composedForward_comp_id
    pair

/-- Public wrapper: the left forward interpretation has the left trace hom. -/
theorem AnalyticMotivesRoot.composablePair_leftForward_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward.traceHom =
      pair.left.traceHom :=
  TraceAnalyticMotive.composablePair_leftForward_traceHom
    pair

/-- Public wrapper: the right forward-before-transport map has the right trace hom. -/
theorem AnalyticMotivesRoot.composablePair_rightForwardBeforeTransport_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport.traceHom =
      pair.right.traceHom :=
  TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_traceHom
    pair

/-- Public wrapper: the composed forward map has composite trace hom. -/
theorem AnalyticMotivesRoot.composablePair_composedForward_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.traceHom =
      pair.leftForward.traceHom ≫ pair.rightForward.traceHom :=
  TraceAnalyticMotive.composablePair_composedForward_traceHom
    pair

/-- Public wrapper: the composed forward trace hom has the left input trace hom first. -/
theorem AnalyticMotivesRoot.composablePair_composedForward_traceHom_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.traceHom =
      pair.left.traceHom ≫ pair.rightForward.traceHom :=
  TraceAnalyticMotive.composablePair_composedForward_traceHom_left
    pair

/-- Public wrapper: left identity for the trace hom of the composed forward map. -/
theorem AnalyticMotivesRoot.composablePair_id_comp_composedForward_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    ((𝟙 pair.sourceGenerator : pair.sourceGenerator ⟶ pair.sourceGenerator) ≫
        pair.composedForward).traceHom =
      pair.composedForward.traceHom :=
  TraceAnalyticMotive.composablePair_id_comp_composedForward_traceHom
    pair

/-- Public wrapper: right identity for the trace hom of the composed forward map. -/
theorem AnalyticMotivesRoot.composablePair_composedForward_comp_id_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (pair.composedForward ≫
        (𝟙 pair.targetGenerator : pair.targetGenerator ⟶ pair.targetGenerator)).traceHom =
      pair.composedForward.traceHom :=
  TraceAnalyticMotive.composablePair_composedForward_comp_id_traceHom
    pair

/-- Public wrapper: the left forward interpretation induces the left input map. -/
theorem AnalyticMotivesRoot.composablePair_leftForward_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward.representableMap =
      pair.left.map :=
  TraceAnalyticMotive.composablePair_leftForward_representableMap
    pair

/-- Public wrapper: the right forward-before-transport map induces the right input map. -/
theorem AnalyticMotivesRoot.composablePair_rightForwardBeforeTransport_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport.representableMap =
      pair.right.map :=
  TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_representableMap
    pair

/-- Public wrapper: the composed forward map has composite representable map. -/
theorem AnalyticMotivesRoot.composablePair_composedForward_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.representableMap =
      pair.leftForward.representableMap ≫ pair.rightForward.representableMap :=
  TraceAnalyticMotive.composablePair_composedForward_representableMap
    pair

/-- Public wrapper: the composed forward representable map has the left input map first. -/
theorem AnalyticMotivesRoot.composablePair_composedForward_representableMap_left
    (pair : TraceLocalizationInputComposablePair) :
    pair.composedForward.representableMap =
      pair.left.map ≫ pair.rightForward.representableMap :=
  TraceAnalyticMotive.composablePair_composedForward_representableMap_left
    pair

/-- Public wrapper: left identity for the representable map of the composed forward map. -/
theorem AnalyticMotivesRoot.composablePair_id_comp_composedForward_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    ((𝟙 pair.sourceGenerator : pair.sourceGenerator ⟶ pair.sourceGenerator) ≫
        pair.composedForward).representableMap =
      pair.composedForward.representableMap :=
  TraceAnalyticMotive.composablePair_id_comp_composedForward_representableMap
    pair

/-- Public wrapper: right identity for the representable map of the composed forward map. -/
theorem AnalyticMotivesRoot.composablePair_composedForward_comp_id_representableMap
    (pair : TraceLocalizationInputComposablePair) :
    (pair.composedForward ≫
        (𝟙 pair.targetGenerator : pair.targetGenerator ⟶ pair.targetGenerator)).representableMap =
      pair.composedForward.representableMap :=
  TraceAnalyticMotive.composablePair_composedForward_comp_id_representableMap
    pair

/-- Public wrapper: the presheaf functor sends the left forward map to the left input map. -/
theorem AnalyticMotivesRoot.composablePair_leftForward_presheafFunctor_map
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map pair.leftForward =
      pair.left.map :=
  TraceAnalyticMotive.composablePair_leftForward_presheafFunctor_map
    pair

/-- Public wrapper: the presheaf functor sends the right forward-before-transport map to the right input map. -/
theorem AnalyticMotivesRoot.composablePair_rightForwardBeforeTransport_presheafFunctor_map
    (pair : TraceLocalizationInputComposablePair) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map
        pair.rightForwardBeforeTransport =
      pair.right.map :=
  TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_presheafFunctor_map
    pair

/-- Public wrapper: the lifted left forward map is the Yoneda map of the left trace hom. -/
theorem AnalyticMotivesRoot.composablePair_leftForward_representableObjectMap_eq_yoneda
    (pair : TraceLocalizationInputComposablePair) :
    pair.leftForward.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map pair.left.traceHom :=
  TraceAnalyticMotive.composablePair_leftForward_representableObjectMap_eq_yoneda
    pair

/-- Public wrapper: the lifted right forward-before-transport map is the Yoneda map of the right trace hom. -/
theorem AnalyticMotivesRoot.composablePair_rightForwardBeforeTransport_representableObjectMap_eq_yoneda
    (pair : TraceLocalizationInputComposablePair) :
    pair.rightForwardBeforeTransport.representableObjectMap =
      (TraceCorQRepresentablePresheaf.yoneda).map pair.right.traceHom :=
  TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_representableObjectMap_eq_yoneda
    pair

/-- Public wrapper: including the lifted left forward map recovers the left input map. -/
theorem AnalyticMotivesRoot.composablePair_leftForward_representableObjectMap_inclusion
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQRepresentablePresheaf.inclusion.map
        pair.leftForward.representableObjectMap =
      pair.left.map :=
  TraceAnalyticMotive.composablePair_leftForward_representableObjectMap_inclusion
    pair

/-- Public wrapper: including the lifted right forward-before-transport map recovers the right input map. -/
theorem AnalyticMotivesRoot.composablePair_rightForwardBeforeTransport_representableObjectMap_inclusion
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQRepresentablePresheaf.inclusion.map
        pair.rightForwardBeforeTransport.representableObjectMap =
      pair.right.map :=
  TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_representableObjectMap_inclusion
    pair

/-- Public wrapper: scalar multiplication of the left forward interpretation is trace scalar multiplication. -/
theorem AnalyticMotivesRoot.composablePair_leftForward_smul_traceHom
    (pair : TraceLocalizationInputComposablePair)
    (coefficient : Rat) :
    (coefficient • pair.leftForward).traceHom =
      coefficient • pair.left.traceHom :=
  TraceAnalyticMotive.composablePair_leftForward_smul_traceHom
    pair
    coefficient

/-- Public wrapper: scalar multiplication of the right forward-before-transport map is trace scalar multiplication. -/
theorem AnalyticMotivesRoot.composablePair_rightForwardBeforeTransport_smul_traceHom
    (pair : TraceLocalizationInputComposablePair)
    (coefficient : Rat) :
    (coefficient • pair.rightForwardBeforeTransport).traceHom =
      coefficient • pair.right.traceHom :=
  TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_smul_traceHom
    pair
    coefficient

/-- Public wrapper: the zero compact morphism on the left pair segment has zero trace hom. -/
theorem AnalyticMotivesRoot.composablePair_leftZero_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (0 : pair.sourceGenerator ⟶ pair.middleGenerator).traceHom =
      (0 : pair.sourceObject ⟶ pair.middleObject) :=
  TraceAnalyticMotive.composablePair_leftZero_traceHom
    pair

/-- Public wrapper: the zero compact morphism on the right-before-transport segment has zero trace hom. -/
theorem AnalyticMotivesRoot.composablePair_rightZeroBeforeTransport_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (0 : pair.right.sourceGenerator ⟶ pair.targetGenerator).traceHom =
      (0 : pair.right.sourceObject ⟶ pair.targetObject) :=
  TraceAnalyticMotive.composablePair_rightZeroBeforeTransport_traceHom
    pair

/-- Public wrapper: negating the left forward interpretation negates its trace hom. -/
theorem AnalyticMotivesRoot.composablePair_leftForward_traceNeg_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (TraceCorQHom.neg pair.leftForward).traceHom =
      TraceCorQHom.neg pair.left.traceHom :=
  TraceAnalyticMotive.composablePair_leftForward_traceNeg_traceHom
    pair

/-- Public wrapper: negating the right forward-before-transport map negates its trace hom. -/
theorem AnalyticMotivesRoot.composablePair_rightForwardBeforeTransport_traceNeg_traceHom
    (pair : TraceLocalizationInputComposablePair) :
    (TraceCorQHom.neg pair.rightForwardBeforeTransport).traceHom =
      TraceCorQHom.neg pair.right.traceHom :=
  TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_traceNeg_traceHom
    pair

/-- Public wrapper: subtracting the left forward interpretation from itself gives zero. -/
theorem AnalyticMotivesRoot.composablePair_leftForward_traceSub_self
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQHom.sub pair.leftForward pair.leftForward =
      TraceCorQHom.zero pair.sourceObject pair.middleObject :=
  TraceAnalyticMotive.composablePair_leftForward_traceSub_self
    pair

/-- Public wrapper: subtracting the right forward-before-transport map from itself gives zero. -/
theorem AnalyticMotivesRoot.composablePair_rightForwardBeforeTransport_traceSub_self
    (pair : TraceLocalizationInputComposablePair) :
    TraceCorQHom.sub
        pair.rightForwardBeforeTransport
        pair.rightForwardBeforeTransport =
      TraceCorQHom.zero pair.right.sourceObject pair.targetObject :=
  TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_traceSub_self
    pair

/-- Public wrapper: scalar multiplication distributes over self-subtraction of the left forward interpretation. -/
theorem AnalyticMotivesRoot.composablePair_leftForward_traceSmul_sub_self
    (pair : TraceLocalizationInputComposablePair)
    (coefficient : Rat) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub pair.leftForward pair.leftForward) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient pair.leftForward)
        (TraceCorQHom.smul coefficient pair.leftForward) :=
  TraceAnalyticMotive.composablePair_leftForward_traceSmul_sub_self
    pair
    coefficient

/-- Public wrapper: scalar multiplication distributes over self-subtraction of the right forward-before-transport map. -/
theorem AnalyticMotivesRoot.composablePair_rightForwardBeforeTransport_traceSmul_sub_self
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
  TraceAnalyticMotive.composablePair_rightForwardBeforeTransport_traceSmul_sub_self
    pair
    coefficient

end AnalyticMotives
end LFunctions
end Boundary
