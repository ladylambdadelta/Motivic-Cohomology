import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.ForwardInterpretations.InputFactors.Owner

/-!
# Three-input formulas for composable-triple forward composites

This file substitutes the three underlying localization inputs into the
left- and right-associated triple forward composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated trace hom is the left parenthesization of the three input trace homs. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedForward_traceHom_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.traceHom =
      (triple.first.traceHom ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.leftPair with
          | rfl => triple.second.traceHom)) ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.third.traceHom) :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedForward_traceHom triple)
    (Eq.trans
      (congrArg
        (fun traceHom =>
          (traceHom ≫ triple.secondForward.traceHom) ≫
            triple.thirdForward.traceHom)
        (TraceLocalizationInputComposableTriple.firstForward_traceHom triple))
      (Eq.trans
        (congrArg
          (fun traceHom =>
            (triple.first.traceHom ≫ traceHom) ≫
              triple.thirdForward.traceHom)
          (TraceLocalizationInputComposableTriple.secondForward_traceHom_eq_transport
            triple))
        (congrArg
          (fun traceHom =>
            (triple.first.traceHom ≫
              (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
                  triple.leftPair with
              | rfl => triple.second.traceHom)) ≫ traceHom)
          (TraceLocalizationInputComposableTriple.thirdForward_traceHom_eq_transport
            triple))))

/-- The right-associated trace hom is the right parenthesization of the three input trace homs. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedForward_traceHom_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.traceHom =
      triple.first.traceHom ≫
        ((match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.second.traceHom) ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.rightPair with
          | rfl => triple.third.traceHom)) :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedForward_traceHom triple)
    (Eq.trans
      (congrArg
        (fun traceHom =>
          traceHom ≫
            (triple.secondForward.traceHom ≫ triple.thirdForward.traceHom))
        (TraceLocalizationInputComposableTriple.firstForward_traceHom triple))
      (Eq.trans
        (congrArg
          (fun traceHom =>
            triple.first.traceHom ≫
              (traceHom ≫ triple.thirdForward.traceHom))
          (TraceLocalizationInputComposableTriple.secondForward_traceHom_eq_transport
            triple))
        (congrArg
          (fun traceHom =>
            triple.first.traceHom ≫
              ((match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
                  triple.leftPair with
              | rfl => triple.second.traceHom) ≫ traceHom))
          (TraceLocalizationInputComposableTriple.thirdForward_traceHom_eq_transport
            triple))))

/-- The left-associated representable map is the left parenthesization of the three input maps. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedForward_representableMap_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.representableMap =
      (triple.first.map ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.leftPair with
          | rfl => triple.second.map)) ≫
        (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.rightPair with
        | rfl => triple.third.map) :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.leftAssociatedForward_representableMap triple)
    (Eq.trans
      (congrArg
        (fun map =>
          (map ≫ triple.secondForward.representableMap) ≫
            triple.thirdForward.representableMap)
        (TraceLocalizationInputComposableTriple.firstForward_representableMap triple))
      (Eq.trans
        (congrArg
          (fun map =>
            (triple.first.map ≫ map) ≫
              triple.thirdForward.representableMap)
          (TraceLocalizationInputComposableTriple.secondForward_representableMap_eq_transport
            triple))
        (congrArg
          (fun map =>
            (triple.first.map ≫
              (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
                  triple.leftPair with
              | rfl => triple.second.map)) ≫ map)
          (TraceLocalizationInputComposableTriple.thirdForward_representableMap_eq_transport
            triple))))

/-- The right-associated representable map is the right parenthesization of the three input maps. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedForward_representableMap_inputs
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.representableMap =
      triple.first.map ≫
        ((match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
            triple.leftPair with
        | rfl => triple.second.map) ≫
          (match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
              triple.rightPair with
          | rfl => triple.third.map)) :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.rightAssociatedForward_representableMap triple)
    (Eq.trans
      (congrArg
        (fun map =>
          map ≫
            (triple.secondForward.representableMap ≫
              triple.thirdForward.representableMap))
        (TraceLocalizationInputComposableTriple.firstForward_representableMap triple))
      (Eq.trans
        (congrArg
          (fun map =>
            triple.first.map ≫
              (map ≫ triple.thirdForward.representableMap))
          (TraceLocalizationInputComposableTriple.secondForward_representableMap_eq_transport
            triple))
        (congrArg
          (fun map =>
            triple.first.map ≫
              ((match TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
                  triple.leftPair with
              | rfl => triple.second.map) ≫ map))
          (TraceLocalizationInputComposableTriple.thirdForward_representableMap_eq_transport
            triple))))

end AnalyticMotives
end LFunctions
end Boundary
