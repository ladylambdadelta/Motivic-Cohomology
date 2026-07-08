import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.Owner

/-!
# Forward compact interpretations for composable triples

This file builds the two parenthesized compact forward composites attached to
a composable triple and proves they agree by compact-generator associativity.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The first forward compact interpretation in a composable triple. -/
def TraceLocalizationInputComposableTriple.firstForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceGenerator ⟶ triple.firstMiddleGenerator :=
  triple.first.unstableForwardCompactInterpretation

/-- The second forward compact interpretation transported across the first middle endpoint. -/
def TraceLocalizationInputComposableTriple.secondForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleGenerator ⟶ triple.secondMiddleGenerator :=
  triple.leftPair.rightForward

/-- The third forward compact interpretation transported across the second middle endpoint. -/
def TraceLocalizationInputComposableTriple.thirdForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleGenerator ⟶ triple.targetGenerator :=
  triple.rightPair.rightForward

/-- The left-associated compact forward composite of a composable triple. -/
def TraceLocalizationInputComposableTriple.leftAssociatedForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceGenerator ⟶ triple.targetGenerator :=
  triple.leftPair.composedForward ≫ triple.thirdForward

/-- The right-associated compact forward composite of a composable triple. -/
def TraceLocalizationInputComposableTriple.rightAssociatedForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceGenerator ⟶ triple.targetGenerator :=
  match TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_second_source
      triple with
  | rfl => triple.firstForward ≫ triple.rightPair.composedForward

/-- The first forward interpretation is the first input forward interpretation. -/
theorem TraceLocalizationInputComposableTriple.firstForward_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstForward =
      triple.first.unstableForwardCompactInterpretation :=
  rfl

/-- The second forward interpretation is the right arrow of the first adjacent pair. -/
theorem TraceLocalizationInputComposableTriple.secondForward_eq_leftPair_rightForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondForward =
      triple.leftPair.rightForward :=
  rfl

/-- The third forward interpretation is the right arrow of the second adjacent pair. -/
theorem TraceLocalizationInputComposableTriple.thirdForward_eq_rightPair_rightForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.thirdForward =
      triple.rightPair.rightForward :=
  rfl

/-- The left-associated composite is the first pair composite followed by the third arrow. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedForward_eq_comp
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward =
      triple.leftPair.composedForward ≫ triple.thirdForward :=
  rfl

/-- The right-associated composite is transported across the first middle endpoint. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedForward_eq_transport
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward =
      match TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_second_source
          triple with
      | rfl => triple.firstForward ≫ triple.rightPair.composedForward :=
  rfl

/-- Left identity for the left-associated forward composite. -/
theorem TraceLocalizationInputComposableTriple.id_comp_leftAssociatedForward
    (triple : TraceLocalizationInputComposableTriple) :
    (𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.leftAssociatedForward =
      triple.leftAssociatedForward :=
  TraceCorQHom.left_id
    triple.leftAssociatedForward

/-- Right identity for the left-associated forward composite. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedForward_comp_id
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator) =
      triple.leftAssociatedForward :=
  TraceCorQHom.right_id
    triple.leftAssociatedForward

/-- Left identity for the right-associated forward composite. -/
theorem TraceLocalizationInputComposableTriple.id_comp_rightAssociatedForward
    (triple : TraceLocalizationInputComposableTriple) :
    (𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.rightAssociatedForward =
      triple.rightAssociatedForward :=
  TraceCorQHom.left_id
    triple.rightAssociatedForward

/-- Right identity for the right-associated forward composite. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedForward_comp_id
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator) =
      triple.rightAssociatedForward :=
  TraceCorQHom.right_id
    triple.rightAssociatedForward

/-- The first adjacent pair left forward map is the triple first forward map. -/
theorem TraceLocalizationInputComposableTriple.leftPair_leftForward_eq_firstForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.leftForward =
      triple.firstForward :=
  rfl

/-- The first adjacent pair right forward map is the triple second forward map. -/
theorem TraceLocalizationInputComposableTriple.leftPair_rightForward_eq_secondForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftPair.rightForward =
      triple.secondForward :=
  rfl

/-- The second adjacent pair left forward map is the triple second arrow before transport. -/
theorem TraceLocalizationInputComposableTriple.rightPair_leftForward_eq_second_input
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.leftForward =
      triple.second.unstableForwardCompactInterpretation :=
  rfl

/-- The second adjacent pair right forward map is the triple third forward map. -/
theorem TraceLocalizationInputComposableTriple.rightPair_rightForward_eq_thirdForward
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightPair.rightForward =
      triple.thirdForward :=
  rfl

/-- The two parenthesized forward compact composites of a composable triple agree. -/
theorem TraceLocalizationInputComposableTriple.associatedForward_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward =
      triple.rightAssociatedForward :=
  match TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_second_source
      triple with
  | rfl =>
      TraceCorQHom.comp_assoc
        triple.firstForward
        triple.secondForward
        triple.thirdForward

/-- The trace homs of the two parenthesized forward compact composites agree. -/
theorem TraceLocalizationInputComposableTriple.associatedForward_traceHom_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.traceHom =
      triple.rightAssociatedForward.traceHom :=
  congrArg
    (fun morphism =>
      morphism.traceHom)
    (TraceLocalizationInputComposableTriple.associatedForward_eq triple)

/-- Left identity for the trace hom of the left-associated composite. -/
theorem TraceLocalizationInputComposableTriple.id_comp_leftAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.leftAssociatedForward).traceHom =
      triple.leftAssociatedForward.traceHom :=
  congrArg
    (fun morphism =>
      morphism.traceHom)
    (TraceLocalizationInputComposableTriple.id_comp_leftAssociatedForward triple)

/-- Right identity for the trace hom of the left-associated composite. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedForward_comp_id_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.leftAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).traceHom =
      triple.leftAssociatedForward.traceHom :=
  congrArg
    (fun morphism =>
      morphism.traceHom)
    (TraceLocalizationInputComposableTriple.leftAssociatedForward_comp_id triple)

/-- Left identity for the trace hom of the right-associated composite. -/
theorem TraceLocalizationInputComposableTriple.id_comp_rightAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.rightAssociatedForward).traceHom =
      triple.rightAssociatedForward.traceHom :=
  congrArg
    (fun morphism =>
      morphism.traceHom)
    (TraceLocalizationInputComposableTriple.id_comp_rightAssociatedForward triple)

/-- Right identity for the trace hom of the right-associated composite. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedForward_comp_id_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.rightAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).traceHom =
      triple.rightAssociatedForward.traceHom :=
  congrArg
    (fun morphism =>
      morphism.traceHom)
    (TraceLocalizationInputComposableTriple.rightAssociatedForward_comp_id triple)

/-- The representable maps of the two parenthesized forward compact composites agree. -/
theorem TraceLocalizationInputComposableTriple.associatedForward_representableMap_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.representableMap =
      triple.rightAssociatedForward.representableMap :=
  congrArg
    (fun morphism =>
      morphism.representableMap)
    (TraceLocalizationInputComposableTriple.associatedForward_eq triple)

/-- Left identity for the representable map of the left-associated composite. -/
theorem TraceLocalizationInputComposableTriple.id_comp_leftAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.leftAssociatedForward).representableMap =
      triple.leftAssociatedForward.representableMap :=
  congrArg
    (fun morphism =>
      morphism.representableMap)
    (TraceLocalizationInputComposableTriple.id_comp_leftAssociatedForward triple)

/-- Right identity for the representable map of the left-associated composite. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedForward_comp_id_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.leftAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).representableMap =
      triple.leftAssociatedForward.representableMap :=
  congrArg
    (fun morphism =>
      morphism.representableMap)
    (TraceLocalizationInputComposableTriple.leftAssociatedForward_comp_id triple)

/-- Left identity for the representable map of the right-associated composite. -/
theorem TraceLocalizationInputComposableTriple.id_comp_rightAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    ((𝟙 triple.sourceGenerator :
        triple.sourceGenerator ⟶ triple.sourceGenerator) ≫
        triple.rightAssociatedForward).representableMap =
      triple.rightAssociatedForward.representableMap :=
  congrArg
    (fun morphism =>
      morphism.representableMap)
    (TraceLocalizationInputComposableTriple.id_comp_rightAssociatedForward triple)

/-- Right identity for the representable map of the right-associated composite. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedForward_comp_id_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.rightAssociatedForward ≫
        (𝟙 triple.targetGenerator :
          triple.targetGenerator ⟶ triple.targetGenerator)).representableMap =
      triple.rightAssociatedForward.representableMap :=
  congrArg
    (fun morphism =>
      morphism.representableMap)
    (TraceLocalizationInputComposableTriple.rightAssociatedForward_comp_id triple)

/-- The left-associated composite has the first two arrows composed before the third. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.traceHom =
      (triple.firstForward.traceHom ≫ triple.secondForward.traceHom) ≫
        triple.thirdForward.traceHom :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.comp_traceHom
      triple.leftPair.composedForward
      triple.thirdForward)
    (congrArg
      (fun traceHom =>
        traceHom ≫ triple.thirdForward.traceHom)
      (TraceLocalizationInputComposablePair.composedForward_traceHom
        triple.leftPair))

/-- The right-associated composite has the first arrow followed by the last two arrows. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedForward_traceHom
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.traceHom =
      triple.firstForward.traceHom ≫
        (triple.secondForward.traceHom ≫ triple.thirdForward.traceHom) :=
  match TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_second_source
      triple with
  | rfl =>
      Eq.trans
        (TraceAnalyticGeometricGenerator.comp_traceHom
          triple.firstForward
          triple.rightPair.composedForward)
        (congrArg
          (fun traceHom =>
            triple.firstForward.traceHom ≫ traceHom)
          (TraceLocalizationInputComposablePair.composedForward_traceHom
            triple.rightPair))

/-- The two explicit three-arrow trace-hom parenthesizations agree. -/
theorem TraceLocalizationInputComposableTriple.associatedForward_explicit_traceHom_eq
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.firstForward.traceHom ≫ triple.secondForward.traceHom) ≫
        triple.thirdForward.traceHom =
      triple.firstForward.traceHom ≫
        (triple.secondForward.traceHom ≫ triple.thirdForward.traceHom) :=
  Eq.trans
    (Eq.symm
      (TraceLocalizationInputComposableTriple.leftAssociatedForward_traceHom
        triple))
    (Eq.trans
      (TraceLocalizationInputComposableTriple.associatedForward_traceHom_eq
        triple)
      (TraceLocalizationInputComposableTriple.rightAssociatedForward_traceHom
        triple))

/-- The left-associated composite has the first two representable maps composed before the third. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedForward.representableMap =
      (triple.firstForward.representableMap ≫ triple.secondForward.representableMap) ≫
        triple.thirdForward.representableMap :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.comp_representableMap
      triple.leftPair.composedForward
      triple.thirdForward)
    (congrArg
      (fun map =>
        map ≫ triple.thirdForward.representableMap)
      (TraceLocalizationInputComposablePair.composedForward_representableMap
        triple.leftPair))

/-- The right-associated composite has the first representable map followed by the last two. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedForward_representableMap
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedForward.representableMap =
      triple.firstForward.representableMap ≫
        (triple.secondForward.representableMap ≫ triple.thirdForward.representableMap) :=
  match TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_second_source
      triple with
  | rfl =>
      Eq.trans
        (TraceAnalyticGeometricGenerator.comp_representableMap
          triple.firstForward
          triple.rightPair.composedForward)
        (congrArg
          (fun map =>
            triple.firstForward.representableMap ≫ map)
          (TraceLocalizationInputComposablePair.composedForward_representableMap
            triple.rightPair))

/-- The two explicit three-arrow representable-map parenthesizations agree. -/
theorem TraceLocalizationInputComposableTriple.associatedForward_explicit_representableMap_eq
    (triple : TraceLocalizationInputComposableTriple) :
    (triple.firstForward.representableMap ≫ triple.secondForward.representableMap) ≫
        triple.thirdForward.representableMap =
      triple.firstForward.representableMap ≫
        (triple.secondForward.representableMap ≫ triple.thirdForward.representableMap) :=
  Eq.trans
    (Eq.symm
      (TraceLocalizationInputComposableTriple.leftAssociatedForward_representableMap
        triple))
    (Eq.trans
      (TraceLocalizationInputComposableTriple.associatedForward_representableMap_eq
        triple)
      (TraceLocalizationInputComposableTriple.rightAssociatedForward_representableMap
        triple))

end AnalyticMotives
end LFunctions
end Boundary
