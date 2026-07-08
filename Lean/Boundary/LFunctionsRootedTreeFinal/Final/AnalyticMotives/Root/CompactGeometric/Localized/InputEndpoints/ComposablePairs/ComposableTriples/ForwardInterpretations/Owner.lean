import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.Owner

/-!
# Public forward interpretations for composable triples

This file exposes the two parenthesized compact forward composites of a
composable triple through the public analytic-motives root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: the first forward map is the first input forward map. -/
theorem AnalyticMotivesRoot.composableTriple_firstForward_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstForward =
      triple.first.unstableForwardCompactInterpretation :=
  TraceAnalyticMotive.composableTriple_firstForward_eq_first
    triple

/-- Public wrapper: the second forward map is the right map of the first pair. -/
theorem AnalyticMotivesRoot.composableTriple_secondForward_eq_leftPair_rightForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondForward =
      triple.leftPair.rightForward :=
  TraceAnalyticMotive.composableTriple_secondForward_eq_leftPair_rightForward
    triple

/-- Public wrapper: the third forward map is the right map of the second pair. -/
theorem AnalyticMotivesRoot.composableTriple_thirdForward_eq_rightPair_rightForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.thirdForward =
      triple.rightPair.rightForward :=
  TraceAnalyticMotive.composableTriple_thirdForward_eq_rightPair_rightForward
    triple

/-- Public wrapper: the left-associated composite is the first pair composite then third. -/
theorem AnalyticMotivesRoot.composableTriple_leftAssociatedForward_eq_comp
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward =
      triple.leftPair.composedForward ≫ triple.thirdForward :=
  TraceAnalyticMotive.composableTriple_leftAssociatedForward_eq_comp
    triple

/-- Public wrapper: the right-associated composite is transported across the first middle. -/
theorem AnalyticMotivesRoot.composableTriple_rightAssociatedForward_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward =
      match TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_second_source
          triple with
      | rfl => triple.firstForward ≫ triple.rightPair.composedForward :=
  TraceAnalyticMotive.composableTriple_rightAssociatedForward_eq_transport
    triple

/-- Public wrapper: left identity for the left-associated forward composite. -/
theorem AnalyticMotivesRoot.composableTriple_id_comp_leftAssociatedForward
    (triple : TraceLocalizationInputComposableTriple) :
    (𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.leftAssociatedForward =
      triple.leftAssociatedForward :=
  TraceAnalyticMotive.composableTriple_id_comp_leftAssociatedForward
    triple

/-- Public wrapper: right identity for the left-associated forward composite. -/
theorem AnalyticMotivesRoot.composableTriple_leftAssociatedForward_comp_id
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator) =
      triple.leftAssociatedForward :=
  TraceAnalyticMotive.composableTriple_leftAssociatedForward_comp_id
    triple

/-- Public wrapper: left identity for the right-associated forward composite. -/
theorem AnalyticMotivesRoot.composableTriple_id_comp_rightAssociatedForward
    (triple : TraceLocalizationInputComposableTriple) :
    (𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.rightAssociatedForward =
      triple.rightAssociatedForward :=
  TraceAnalyticMotive.composableTriple_id_comp_rightAssociatedForward
    triple

/-- Public wrapper: right identity for the right-associated forward composite. -/
theorem AnalyticMotivesRoot.composableTriple_rightAssociatedForward_comp_id
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator) =
      triple.rightAssociatedForward :=
  TraceAnalyticMotive.composableTriple_rightAssociatedForward_comp_id
    triple

/-- Public wrapper: the two parenthesized forward composites agree. -/
theorem AnalyticMotivesRoot.composableTriple_associatedForward_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward =
      triple.rightAssociatedForward :=
  TraceAnalyticMotive.composableTriple_associatedForward_eq
    triple

/-- Public wrapper: the trace homs of the two parenthesized composites agree. -/
theorem AnalyticMotivesRoot.composableTriple_associatedForward_traceHom_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.traceHom =
      triple.rightAssociatedForward.traceHom :=
  TraceAnalyticMotive.composableTriple_associatedForward_traceHom_eq
    triple

/-- Public wrapper: left identity for the trace hom of the left-associated composite. -/
theorem AnalyticMotivesRoot.composableTriple_id_comp_leftAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.leftAssociatedForward).traceHom =
      triple.leftAssociatedForward.traceHom :=
  TraceAnalyticMotive.composableTriple_id_comp_leftAssociatedForward_traceHom
    triple

/-- Public wrapper: right identity for the trace hom of the left-associated composite. -/
theorem AnalyticMotivesRoot.composableTriple_leftAssociatedForward_comp_id_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.leftAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).traceHom =
      triple.leftAssociatedForward.traceHom :=
  TraceAnalyticMotive.composableTriple_leftAssociatedForward_comp_id_traceHom
    triple

/-- Public wrapper: left identity for the trace hom of the right-associated composite. -/
theorem AnalyticMotivesRoot.composableTriple_id_comp_rightAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.rightAssociatedForward).traceHom =
      triple.rightAssociatedForward.traceHom :=
  TraceAnalyticMotive.composableTriple_id_comp_rightAssociatedForward_traceHom
    triple

/-- Public wrapper: right identity for the trace hom of the right-associated composite. -/
theorem AnalyticMotivesRoot.composableTriple_rightAssociatedForward_comp_id_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.rightAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).traceHom =
      triple.rightAssociatedForward.traceHom :=
  TraceAnalyticMotive.composableTriple_rightAssociatedForward_comp_id_traceHom
    triple

/-- Public wrapper: the left-associated trace hom is the left-parenthesized triple product. -/
theorem AnalyticMotivesRoot.composableTriple_leftAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.traceHom =
      (triple.firstForward.traceHom ≫ triple.secondForward.traceHom) ≫
        triple.thirdForward.traceHom :=
  TraceAnalyticMotive.composableTriple_leftAssociatedForward_traceHom
    triple

/-- Public wrapper: the right-associated trace hom is the right-parenthesized triple product. -/
theorem AnalyticMotivesRoot.composableTriple_rightAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.traceHom =
      triple.firstForward.traceHom ≫
        (triple.secondForward.traceHom ≫ triple.thirdForward.traceHom) :=
  TraceAnalyticMotive.composableTriple_rightAssociatedForward_traceHom
    triple

/-- Public wrapper: the explicit trace-hom triple products associate. -/
theorem AnalyticMotivesRoot.composableTriple_associatedForward_explicit_traceHom_eq
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.firstForward.traceHom ≫ triple.secondForward.traceHom) ≫
        triple.thirdForward.traceHom =
      triple.firstForward.traceHom ≫
        (triple.secondForward.traceHom ≫ triple.thirdForward.traceHom) :=
  TraceAnalyticMotive.composableTriple_associatedForward_explicit_traceHom_eq
    triple

/-- Public wrapper: the representable maps of the two parenthesized composites agree. -/
theorem AnalyticMotivesRoot.composableTriple_associatedForward_representableMap_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.representableMap =
      triple.rightAssociatedForward.representableMap :=
  TraceAnalyticMotive.composableTriple_associatedForward_representableMap_eq
    triple

/-- Public wrapper: left identity for the representable map of the left-associated composite. -/
theorem AnalyticMotivesRoot.composableTriple_id_comp_leftAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.leftAssociatedForward).representableMap =
      triple.leftAssociatedForward.representableMap :=
  TraceAnalyticMotive.composableTriple_id_comp_leftAssociatedForward_representableMap
    triple

/-- Public wrapper: right identity for the representable map of the left-associated composite. -/
theorem AnalyticMotivesRoot.composableTriple_leftAssociatedForward_comp_id_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.leftAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).representableMap =
      triple.leftAssociatedForward.representableMap :=
  TraceAnalyticMotive.composableTriple_leftAssociatedForward_comp_id_representableMap
    triple

/-- Public wrapper: left identity for the representable map of the right-associated composite. -/
theorem AnalyticMotivesRoot.composableTriple_id_comp_rightAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.rightAssociatedForward).representableMap =
      triple.rightAssociatedForward.representableMap :=
  TraceAnalyticMotive.composableTriple_id_comp_rightAssociatedForward_representableMap
    triple

/-- Public wrapper: right identity for the representable map of the right-associated composite. -/
theorem AnalyticMotivesRoot.composableTriple_rightAssociatedForward_comp_id_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.rightAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).representableMap =
      triple.rightAssociatedForward.representableMap :=
  TraceAnalyticMotive.composableTriple_rightAssociatedForward_comp_id_representableMap
    triple

/-- Public wrapper: the left-associated representable map is the left triple product. -/
theorem AnalyticMotivesRoot.composableTriple_leftAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.representableMap =
      (triple.firstForward.representableMap ≫ triple.secondForward.representableMap) ≫
        triple.thirdForward.representableMap :=
  TraceAnalyticMotive.composableTriple_leftAssociatedForward_representableMap
    triple

/-- Public wrapper: the right-associated representable map is the right triple product. -/
theorem AnalyticMotivesRoot.composableTriple_rightAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.representableMap =
      triple.firstForward.representableMap ≫
        (triple.secondForward.representableMap ≫ triple.thirdForward.representableMap) :=
  TraceAnalyticMotive.composableTriple_rightAssociatedForward_representableMap
    triple

/-- Public wrapper: the explicit representable-map triple products associate. -/
theorem AnalyticMotivesRoot.composableTriple_associatedForward_explicit_representableMap_eq
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.firstForward.representableMap ≫ triple.secondForward.representableMap) ≫
        triple.thirdForward.representableMap =
      triple.firstForward.representableMap ≫
        (triple.secondForward.representableMap ≫ triple.thirdForward.representableMap) :=
  TraceAnalyticMotive.composableTriple_associatedForward_explicit_representableMap_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
