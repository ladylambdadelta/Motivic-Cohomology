import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.Owner

/-!
# Motive-root forward interpretations for composable triples

This file exposes the two parenthesized compact forward composites of a
composable triple through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: the first forward map is the first input forward map. -/
theorem TraceAnalyticMotive.composableTriple_firstForward_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstForward =
      triple.first.unstableForwardCompactInterpretation :=
  TraceLocalizationInputComposableTriple.firstForward_eq_first
    triple

/-- Motive-root wrapper: the second forward map is the right map of the first pair. -/
theorem TraceAnalyticMotive.composableTriple_secondForward_eq_leftPair_rightForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondForward =
      triple.leftPair.rightForward :=
  TraceLocalizationInputComposableTriple.secondForward_eq_leftPair_rightForward
    triple

/-- Motive-root wrapper: the third forward map is the right map of the second pair. -/
theorem TraceAnalyticMotive.composableTriple_thirdForward_eq_rightPair_rightForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.thirdForward =
      triple.rightPair.rightForward :=
  TraceLocalizationInputComposableTriple.thirdForward_eq_rightPair_rightForward
    triple

/-- Motive-root wrapper: the left-associated composite is the first pair composite then third. -/
theorem TraceAnalyticMotive.composableTriple_leftAssociatedForward_eq_comp
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward =
      triple.leftPair.composedForward ≫ triple.thirdForward :=
  TraceLocalizationInputComposableTriple.leftAssociatedForward_eq_comp
    triple

/-- Motive-root wrapper: the right-associated composite is transported across the first middle. -/
theorem TraceAnalyticMotive.composableTriple_rightAssociatedForward_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward =
      match TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_second_source
          triple with
      | rfl => triple.firstForward ≫ triple.rightPair.composedForward :=
  TraceLocalizationInputComposableTriple.rightAssociatedForward_eq_transport
    triple

/-- Motive-root wrapper: left identity for the left-associated forward composite. -/
theorem TraceAnalyticMotive.composableTriple_id_comp_leftAssociatedForward
    (triple : TraceLocalizationInputComposableTriple) :
    (𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.leftAssociatedForward =
      triple.leftAssociatedForward :=
  TraceLocalizationInputComposableTriple.id_comp_leftAssociatedForward
    triple

/-- Motive-root wrapper: right identity for the left-associated forward composite. -/
theorem TraceAnalyticMotive.composableTriple_leftAssociatedForward_comp_id
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator) =
      triple.leftAssociatedForward :=
  TraceLocalizationInputComposableTriple.leftAssociatedForward_comp_id
    triple

/-- Motive-root wrapper: left identity for the right-associated forward composite. -/
theorem TraceAnalyticMotive.composableTriple_id_comp_rightAssociatedForward
    (triple : TraceLocalizationInputComposableTriple) :
    (𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.rightAssociatedForward =
      triple.rightAssociatedForward :=
  TraceLocalizationInputComposableTriple.id_comp_rightAssociatedForward
    triple

/-- Motive-root wrapper: right identity for the right-associated forward composite. -/
theorem TraceAnalyticMotive.composableTriple_rightAssociatedForward_comp_id
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator) =
      triple.rightAssociatedForward :=
  TraceLocalizationInputComposableTriple.rightAssociatedForward_comp_id
    triple

/-- Motive-root wrapper: the two parenthesized forward composites agree. -/
theorem TraceAnalyticMotive.composableTriple_associatedForward_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward =
      triple.rightAssociatedForward :=
  TraceLocalizationInputComposableTriple.associatedForward_eq
    triple

/-- Motive-root wrapper: the trace homs of the two parenthesized composites agree. -/
theorem TraceAnalyticMotive.composableTriple_associatedForward_traceHom_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.traceHom =
      triple.rightAssociatedForward.traceHom :=
  TraceLocalizationInputComposableTriple.associatedForward_traceHom_eq
    triple

/-- Motive-root wrapper: left identity for the trace hom of the left-associated composite. -/
theorem TraceAnalyticMotive.composableTriple_id_comp_leftAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.leftAssociatedForward).traceHom =
      triple.leftAssociatedForward.traceHom :=
  TraceLocalizationInputComposableTriple.id_comp_leftAssociatedForward_traceHom
    triple

/-- Motive-root wrapper: right identity for the trace hom of the left-associated composite. -/
theorem TraceAnalyticMotive.composableTriple_leftAssociatedForward_comp_id_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.leftAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).traceHom =
      triple.leftAssociatedForward.traceHom :=
  TraceLocalizationInputComposableTriple.leftAssociatedForward_comp_id_traceHom
    triple

/-- Motive-root wrapper: left identity for the trace hom of the right-associated composite. -/
theorem TraceAnalyticMotive.composableTriple_id_comp_rightAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.rightAssociatedForward).traceHom =
      triple.rightAssociatedForward.traceHom :=
  TraceLocalizationInputComposableTriple.id_comp_rightAssociatedForward_traceHom
    triple

/-- Motive-root wrapper: right identity for the trace hom of the right-associated composite. -/
theorem TraceAnalyticMotive.composableTriple_rightAssociatedForward_comp_id_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.rightAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).traceHom =
      triple.rightAssociatedForward.traceHom :=
  TraceLocalizationInputComposableTriple.rightAssociatedForward_comp_id_traceHom
    triple

/-- Motive-root wrapper: the left-associated trace hom is the left-parenthesized triple product. -/
theorem TraceAnalyticMotive.composableTriple_leftAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.traceHom =
      (triple.firstForward.traceHom ≫ triple.secondForward.traceHom) ≫
        triple.thirdForward.traceHom :=
  TraceLocalizationInputComposableTriple.leftAssociatedForward_traceHom
    triple

/-- Motive-root wrapper: the right-associated trace hom is the right-parenthesized triple product. -/
theorem TraceAnalyticMotive.composableTriple_rightAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.traceHom =
      triple.firstForward.traceHom ≫
        (triple.secondForward.traceHom ≫ triple.thirdForward.traceHom) :=
  TraceLocalizationInputComposableTriple.rightAssociatedForward_traceHom
    triple

/-- Motive-root wrapper: the explicit trace-hom triple products associate. -/
theorem TraceAnalyticMotive.composableTriple_associatedForward_explicit_traceHom_eq
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.firstForward.traceHom ≫ triple.secondForward.traceHom) ≫
        triple.thirdForward.traceHom =
      triple.firstForward.traceHom ≫
        (triple.secondForward.traceHom ≫ triple.thirdForward.traceHom) :=
  TraceLocalizationInputComposableTriple.associatedForward_explicit_traceHom_eq
    triple

/-- Motive-root wrapper: the representable maps of the two parenthesized composites agree. -/
theorem TraceAnalyticMotive.composableTriple_associatedForward_representableMap_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.representableMap =
      triple.rightAssociatedForward.representableMap :=
  TraceLocalizationInputComposableTriple.associatedForward_representableMap_eq
    triple

/-- Motive-root wrapper: left identity for the representable map of the left-associated composite. -/
theorem TraceAnalyticMotive.composableTriple_id_comp_leftAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.leftAssociatedForward).representableMap =
      triple.leftAssociatedForward.representableMap :=
  TraceLocalizationInputComposableTriple.id_comp_leftAssociatedForward_representableMap
    triple

/-- Motive-root wrapper: right identity for the representable map of the left-associated composite. -/
theorem TraceAnalyticMotive.composableTriple_leftAssociatedForward_comp_id_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.leftAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).representableMap =
      triple.leftAssociatedForward.representableMap :=
  TraceLocalizationInputComposableTriple.leftAssociatedForward_comp_id_representableMap
    triple

/-- Motive-root wrapper: left identity for the representable map of the right-associated composite. -/
theorem TraceAnalyticMotive.composableTriple_id_comp_rightAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.rightAssociatedForward).representableMap =
      triple.rightAssociatedForward.representableMap :=
  TraceLocalizationInputComposableTriple.id_comp_rightAssociatedForward_representableMap
    triple

/-- Motive-root wrapper: right identity for the representable map of the right-associated composite. -/
theorem TraceAnalyticMotive.composableTriple_rightAssociatedForward_comp_id_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.rightAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).representableMap =
      triple.rightAssociatedForward.representableMap :=
  TraceLocalizationInputComposableTriple.rightAssociatedForward_comp_id_representableMap
    triple

/-- Motive-root wrapper: the left-associated representable map is the left triple product. -/
theorem TraceAnalyticMotive.composableTriple_leftAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.representableMap =
      (triple.firstForward.representableMap ≫ triple.secondForward.representableMap) ≫
        triple.thirdForward.representableMap :=
  TraceLocalizationInputComposableTriple.leftAssociatedForward_representableMap
    triple

/-- Motive-root wrapper: the right-associated representable map is the right triple product. -/
theorem TraceAnalyticMotive.composableTriple_rightAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.representableMap =
      triple.firstForward.representableMap ≫
        (triple.secondForward.representableMap ≫ triple.thirdForward.representableMap) :=
  TraceLocalizationInputComposableTriple.rightAssociatedForward_representableMap
    triple

/-- Motive-root wrapper: the explicit representable-map triple products associate. -/
theorem TraceAnalyticMotive.composableTriple_associatedForward_explicit_representableMap_eq
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.firstForward.representableMap ≫ triple.secondForward.representableMap) ≫
        triple.thirdForward.representableMap =
      triple.firstForward.representableMap ≫
        (triple.secondForward.representableMap ≫ triple.thirdForward.representableMap) :=
  TraceLocalizationInputComposableTriple.associatedForward_explicit_representableMap_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
