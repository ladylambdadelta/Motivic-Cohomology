import TraceCalc.ClassicalPeriods.Reflection

open CategoryTheory

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Scalar-valued probe family on packed structured comparison morphisms. -/
structure ScalarProbeFamily (ctx : ClassicalComparisonContext.{u, v}) where
  ProbeIndex : Type w
  ScalarCarrier : Type x
  probeValue : ProbeIndex → SomeStructuredComparisonMorphism ctx → ScalarCarrier
  equalityRelation : ScalarCarrier → ScalarCarrier → Prop
  probeNaturalityTarget : Prop
  probeExtractionTarget : Prop

/-- Framed probe family carrying honest framed witnesses and their extracted scalar values. -/
structure FramedProbeFamily (ctx : ClassicalComparisonContext.{u, v}) where
  ProbeIndex : Type w
  framedDatum : ProbeIndex → SomeStructuredComparisonMorphism ctx → SomeFramedPeriodDatum ctx
  shadow : ScalarPeriodShadow (SomeFramedPeriodDatum ctx)
  scalarValue : ProbeIndex → SomeStructuredComparisonMorphism ctx → shadow.ScalarCarrier
  scalarValue_agrees_with_shadow : Prop

namespace FramedProbeFamily

/-- Forget the framed witness and keep only the induced scalar-valued probe family. -/
def toScalarProbeFamily
    {ctx : ClassicalComparisonContext.{u, v}}
    (family : FramedProbeFamily ctx) : ScalarProbeFamily ctx where
  ProbeIndex := family.ProbeIndex
  ScalarCarrier := family.shadow.ScalarCarrier
  probeValue := family.scalarValue
  equalityRelation := family.shadow.equalityRelation
  probeNaturalityTarget := True
  probeExtractionTarget := family.scalarValue_agrees_with_shadow

end FramedProbeFamily

/-- Two packed comparison morphisms agree on all probes in a fixed family. -/
def ProbeEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    (family : ScalarProbeFamily ctx)
    (left right : SomeStructuredComparisonMorphism ctx) : Prop :=
  ∀ probe : family.ProbeIndex,
    family.equalityRelation (family.probeValue probe left) (family.probeValue probe right)

/-- Equality on a framed probe family, before forgetting to the scalar probe carrier. -/
def FramedProbeEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    (family : FramedProbeFamily ctx)
    (left right : SomeStructuredComparisonMorphism ctx) : Prop :=
  ProbeEquality family.toScalarProbeFamily left right

/-- Framed-probe equality is already the tomography probe equality of the forgotten scalar family.
-/
theorem framedProbeEquality_to_tomographyProbeEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    (family : FramedProbeFamily ctx)
    (left right : SomeStructuredComparisonMorphism ctx) :
    FramedProbeEquality family left right →
      ProbeEquality family.toScalarProbeFamily left right := by
  intro hEquality
  exact hEquality

/-- Probe equality determines the basis-free period map. -/
structure ProbeExtensionalityForBasisFreePeriodMap
    (ctx : ClassicalComparisonContext.{u, v})
    (family : ScalarProbeFamily ctx)
    (basisEq : BasisFreePeriodMapEquality ctx) where
  theoremTarget :
    ∀ left right : SomeStructuredComparisonMorphism ctx,
      ProbeEquality family left right → basisEq.relates left right

/-- Equality of basis-free period maps determines packed structured comparison equality. -/
structure BasisFreePeriodMapDeterminesPackedComparison
    (ctx : ClassicalComparisonContext.{u, v})
    (basisEq : BasisFreePeriodMapEquality ctx)
    (structuredEq : StructuredComparisonEquality ctx) where
  theoremTarget :
    ∀ left right : SomeStructuredComparisonMorphism ctx,
      basisEq.relates left right → structuredEq.relates left right

/-- Framed equality is sound for the probe family: equal framed witnesses give equal probe values. -/
structure ProbeSoundness
    (C : Type u) [Category.{v} C]
    (ctx : ClassicalComparisonContext.{w, x})
    (family : ScalarProbeFamily ctx)
    (framedEq : FramedPeriodEquality ctx)
    (framedOf : {X Y : C} → (X ⟶ Y) → SomeFramedPeriodDatum ctx)
    (comparisonOf : {X Y : C} → (X ⟶ Y) → SomeStructuredComparisonMorphism ctx) where
  theoremTarget :
    ∀ {X Y : C} (f g : X ⟶ Y),
      framedEq.relates (framedOf f) (framedOf g) →
        ProbeEquality family (comparisonOf f) (comparisonOf g)

/-- Tomography core: probes determine the basis-free period map, and the basis-free period map
then determines the packed structured comparison package. -/
structure ClassicalPeriodTomographyCore
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) where
  probeFamily : ScalarProbeFamily ctx
  basisFreePeriodMapEquality : BasisFreePeriodMapEquality ctx
  probeExtensionality :
    ProbeExtensionalityForBasisFreePeriodMap
      ctx
      probeFamily
      basisFreePeriodMapEquality
  basisFreeDeterminesPacked :
    BasisFreePeriodMapDeterminesPackedComparison
      ctx
      basisFreePeriodMapEquality
      structuredEq

/-- The main tomography consequence: agreement on all probes implies packed structured comparison
agreement. -/
theorem ClassicalPeriodTomographyCore.toStructuredComparisonEquality
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (core : ClassicalPeriodTomographyCore ctx structuredEq)
    (left right : SomeStructuredComparisonMorphism ctx) :
    ProbeEquality core.probeFamily left right → structuredEq.relates left right := by
  intro hProbe
  exact core.basisFreeDeterminesPacked.theoremTarget
    left
    right
    (core.probeExtensionality.theoremTarget left right hProbe)

/-- Manuscript-facing name for the second tomography stage: reconstruction of packed structured
comparison data from the basis-free period map. -/
abbrev PackedComparisonFromBasisFreePeriodMap :=
  BasisFreePeriodMapDeterminesPackedComparison

/-- Assembly theorem for the sigma-packed tomography core. This is the target-facing bridge from
the named probe-separation and reconstruction stages to `ClassicalPeriodTomographyCore`. -/
def separatingProbeFamily_to_ClassicalPeriodTomographyCore
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (family : ScalarProbeFamily ctx)
    (basisEq : BasisFreePeriodMapEquality ctx)
    (probeExtensionality : ProbeExtensionalityForBasisFreePeriodMap ctx family basisEq)
    (reconstruction : PackedComparisonFromBasisFreePeriodMap ctx basisEq structuredEq) :
    ClassicalPeriodTomographyCore ctx structuredEq where
  probeFamily := family
  basisFreePeriodMapEquality := basisEq
  probeExtensionality := probeExtensionality
  basisFreeDeterminesPacked := reconstruction

/-- Cheap tautological tomography core: probes are indexed by the compared packed datum itself and
probe equality is just structured comparison equality. -/
def tautologicalScalarProbeFamily
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) :
    ScalarProbeFamily ctx where
  ProbeIndex := PUnit
  ScalarCarrier := SomeStructuredComparisonMorphism ctx
  probeValue := fun _ datum => datum
  equalityRelation := structuredEq.relates
  probeNaturalityTarget := True
  probeExtractionTarget := True

/-- Shorter manuscript-facing alias for the tautological sanity probe family. -/
abbrev tautologicalProbeFamily := tautologicalScalarProbeFamily

/-- Cheap tautological basis-free equality target used only as a sanity witness. -/
def tautologicalBasisFreePeriodMapEquality
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) :
    BasisFreePeriodMapEquality ctx where
  relates := structuredEq.relates
  reflexiveTarget := structuredEq.reflexiveTarget
  symmetricTarget := structuredEq.symmetricTarget
  transitiveTarget := structuredEq.transitiveTarget

/-- Cheap tautological tomography core. -/
def tautologicalTomographyCore
    (ctx : ClassicalComparisonContext.{u, v})
    (structuredEq : StructuredComparisonEquality ctx) :
    ClassicalPeriodTomographyCore ctx structuredEq where
  probeFamily := tautologicalScalarProbeFamily ctx structuredEq
  basisFreePeriodMapEquality := tautologicalBasisFreePeriodMapEquality ctx structuredEq
  probeExtensionality := {
    theoremTarget := by
      intro left right hProbe
      exact hProbe PUnit.unit
  }
  basisFreeDeterminesPacked := {
    theoremTarget := by
      intro left right hBasis
      exact hBasis
  }

end ClassicalPeriods
end TraceCalc
