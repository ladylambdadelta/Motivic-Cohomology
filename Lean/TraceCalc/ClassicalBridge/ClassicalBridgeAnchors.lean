import TraceCalc.ClassicalPeriods.PeriodConjectureTarget
import TraceCalc.ClassicalPeriods.ReverseMath

open CategoryTheory

universe u v w x y

namespace TraceCalc
namespace ClassicalBridge

/-- Bridge-local source-side localization contract. The classical target modules currently start at
structured comparison and period-faithfulness objects, so the source presentation slot remains a
middleware adapter surface. -/
structure ClassicalLocalization
    (Source : Type u) (Target : Type v) [Category.{w} Source] [Category.{w} Target] where
  weakEquivalence : Source → Source → Prop
  localizationFunctor : ClassicalPeriods.ClassicalFunctor Source Target
  LocalizationWitness : Type x
  localizationWitness : LocalizationWitness
  universalProperty : Prop

/-- Bridge-local source-side classical presentation contract. This remains middleware-specific
because the ClassicalPeriods target lane does not yet define a source-presentation object. -/
structure ClassicalMotivicPresentation where
  Syntax : Type u
  SourceCategory : Type v
  LocalizedCategory : Type w
  [catSource : Category.{x} SourceCategory]
  [catLocalized : Category.{x} LocalizedCategory]
  includeSyntax : Syntax → SourceCategory
  localization : ClassicalLocalization SourceCategory LocalizedCategory
  GeometricShapeData : Type y
  geometricShapeData : GeometricShapeData
  geometricShapeAxioms : Prop

attribute [instance] ClassicalMotivicPresentation.catSource ClassicalMotivicPresentation.catLocalized

/-- Mathlib-facing functor alias re-exported from the real ClassicalPeriods target lane. -/
abbrev ClassicalFunctor := ClassicalPeriods.ClassicalFunctor

/-- Shared scalar context for the classical comparison lane. -/
abbrev ClassicalComparisonContext := ClassicalPeriods.ClassicalComparisonContext

/-- Real classical structured comparison object, owned by the ClassicalPeriods target lane. -/
abbrev ClassicalStructuredComparisonObject
    (ctx : ClassicalComparisonContext) :=
  ClassicalPeriods.ClassicalStructuredComparisonObject ctx

/-- Real morphism-level structured comparison data, owned by the ClassicalPeriods target lane. -/
abbrev ClassicalStructuredComparisonMorphism
    (ctx : ClassicalComparisonContext)
    (source target : ClassicalStructuredComparisonObject ctx) :=
  ClassicalPeriods.ClassicalStructuredComparisonMorphism source target

/-- Sigma-packaged morphism-level structured comparison surface. -/
abbrev SomeStructuredComparisonMorphism
    (ctx : ClassicalComparisonContext) :=
  ClassicalPeriods.SomeStructuredComparisonMorphism ctx

/-- Equality package for morphism-level structured comparison data. -/
abbrev StructuredComparisonEquality
    (ctx : ClassicalComparisonContext) :=
  ClassicalPeriods.StructuredComparisonEquality ctx

/-- Real scalar-shadow interface, owned by the ClassicalPeriods target lane. -/
abbrev ScalarPeriodShadow
    (carrier : Type u) :=
  ClassicalPeriods.ScalarPeriodShadow carrier

/-- Equality package for scalar-shadow data. -/
abbrev ScalarShadowEquality
    (carrier : Type u)
    (shadow : ScalarPeriodShadow carrier) :=
  ClassicalPeriods.ScalarShadowEquality carrier shadow

/-- Real framed-period pairing contract, owned by the ClassicalPeriods target lane. -/
abbrev PeriodPairingData
    (ctx : ClassicalComparisonContext)
    {source target : ClassicalStructuredComparisonObject ctx}
    (morphism : ClassicalStructuredComparisonMorphism ctx source target) :=
  ClassicalPeriods.PeriodPairingData morphism

/-- Real framed-period datum, owned by the ClassicalPeriods target lane. -/
abbrev FramedPeriodDatum
    (ctx : ClassicalComparisonContext)
    {source target : ClassicalStructuredComparisonObject ctx}
    {morphism : ClassicalStructuredComparisonMorphism ctx source target}
    (pairingData : PeriodPairingData ctx morphism) :=
  ClassicalPeriods.FramedPeriodDatum morphism pairingData

/-- Sigma-packaged framed-period witness type from the ClassicalPeriods target lane. -/
abbrev SomeFramedPeriodDatum
    (ctx : ClassicalComparisonContext) :=
  ClassicalPeriods.SomeFramedPeriodDatum ctx

/-- Equality package for framed-period data. -/
abbrev FramedPeriodEquality
    (ctx : ClassicalComparisonContext) :=
  ClassicalPeriods.FramedPeriodEquality ctx

/-- Framed-period operations surface from the ClassicalPeriods target lane. -/
abbrev FramedPeriodOperations
    (ctx : ClassicalComparisonContext) :=
  ClassicalPeriods.FramedPeriodOperations ctx

/-- Real classical Grothendieck period-faithfulness target. -/
abbrev ClassicalGrothendieckPeriodFaithfulnessTarget :=
  ClassicalPeriods.ClassicalGrothendieckPeriodFaithfulnessTarget

/-- Stable exported final classical theorem target. -/
abbrev ClassicalGrothendieckPeriodFaithfulnessStatement :=
  ClassicalPeriods.ClassicalGrothendieckPeriodFaithfulnessStatement

/-- Real framed refinement of the classical target. -/
abbrev FramedPeriodConjectureTarget := ClassicalPeriods.FramedPeriodConjectureTarget

/-- Stable exported framed-period theorem target. -/
abbrev ClassicalFramedPeriodConjectureStatement :=
  ClassicalPeriods.ClassicalFramedPeriodConjectureStatement

/-- Real reverse-mathematics obligation package for the classical target lane. -/
abbrev ClassicalPeriodReverseMathObligations :=
  ClassicalPeriods.ClassicalPeriodReverseMathObligations

/-- Real reverse-mathematics input surface for the classical target lane. -/
abbrev ClassicalPeriodTargetInputsFromTraceProgram :=
  ClassicalPeriods.ClassicalPeriodTargetInputsFromTraceProgram

end ClassicalBridge
end TraceCalc