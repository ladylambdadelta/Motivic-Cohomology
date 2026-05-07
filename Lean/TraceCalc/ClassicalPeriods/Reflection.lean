import TraceCalc.ClassicalPeriods.Framed
import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

/-- Equality layer for full structured comparison morphism packages. -/
abbrev StructuredComparisonMorphismEquality := StructuredComparisonEquality

/-- Equality layer for basis-free period maps.

This relation is kept abstract because the underlying source/target objects vary across sigma-packed
comparison data, so direct function equality is not always the right transport-free surface. -/
structure BasisFreePeriodMapEquality (ctx : ClassicalComparisonContext.{u, v}) where
  relates : SomeStructuredComparisonMorphism ctx → SomeStructuredComparisonMorphism ctx → Prop
  reflexiveTarget : Prop
  symmetricTarget : Prop
  transitiveTarget : Prop

/-- Equality layer for motive morphisms. -/
structure MotiveMorphismEqualityTarget (C : Type u) [Category.{v} C] where
  relates : {X Y : C} → (X ⟶ Y) → (X ⟶ Y) → Prop
  reflexiveTarget : Prop
  symmetricTarget : Prop
  transitiveTarget : Prop

/-- Default motive-morphism equality target given by literal equality. -/
def definitionalMotiveMorphismEqualityTarget
    (C : Type u) [Category.{v} C] : MotiveMorphismEqualityTarget C where
  relates := fun {_ _} f g => f = g
  reflexiveTarget := ∀ {X Y : C} (f : X ⟶ Y), f = f
  symmetricTarget := ∀ {X Y : C} (f g : X ⟶ Y), f = g → g = f
  transitiveTarget := ∀ {X Y : C} (f g h : X ⟶ Y), f = g → g = h → f = h

/-- Basis-free period-map equality reflects structured comparison equality. -/
structure BasisFreePeriodMapReflectsStructuredComparison
    (ctx : ClassicalComparisonContext.{u, v})
    (basisEq : BasisFreePeriodMapEquality ctx)
    (structuredEq : StructuredComparisonEquality ctx) where
  theoremTarget :
    ∀ left right : SomeStructuredComparisonMorphism ctx,
      basisEq.relates left right → structuredEq.relates left right

/-- Scalar-shadow equality reflects framed-period equality. -/
structure ScalarShadowReflectsFramedEquality
    (ctx : ClassicalComparisonContext.{u, v})
    (framedEq : FramedPeriodEquality ctx)
    (shadow : ScalarPeriodShadow (SomeFramedPeriodDatum ctx)) where
  theoremTarget :
    ∀ left right : SomeFramedPeriodDatum ctx,
      shadow.equalityRelation (shadow.shadowOf left) (shadow.shadowOf right) →
        framedEq.relates left right

/-- Framed-period equality reflects structured comparison equality. -/
structure FramedEqualityReflectsStructuredComparison
    (ctx : ClassicalComparisonContext.{u, v})
    (framedEq : FramedPeriodEquality ctx)
    (structuredEq : StructuredComparisonEquality ctx)
    (structuredOf : SomeFramedPeriodDatum ctx → SomeStructuredComparisonMorphism ctx) where
  theoremTarget :
    ∀ left right : SomeFramedPeriodDatum ctx,
      framedEq.relates left right →
        structuredEq.relates (structuredOf left) (structuredOf right)

/-- Scalar-shadow equality reflects structured comparison equality directly. -/
structure ScalarShadowReflectsStructuredComparison
    (ctx : ClassicalComparisonContext.{u, v})
    (shadow : ScalarPeriodShadow (SomeFramedPeriodDatum ctx))
    (structuredEq : StructuredComparisonEquality ctx)
    (structuredOf : SomeFramedPeriodDatum ctx → SomeStructuredComparisonMorphism ctx) where
  theoremTarget :
    ∀ left right : SomeFramedPeriodDatum ctx,
      shadow.equalityRelation (shadow.shadowOf left) (shadow.shadowOf right) →
        structuredEq.relates (structuredOf left) (structuredOf right)

/-- The four equality levels that appear in the classical period ladder. -/
structure ClassicalPeriodEqualityLadder
    (C : Type u) [Category.{v} C]
    (ctx : ClassicalComparisonContext.{w, x})
    (framedShadow : ScalarPeriodShadow (SomeFramedPeriodDatum ctx))
    (framedEq : FramedPeriodEquality ctx)
    (structuredEq : StructuredComparisonEquality ctx)
    (morphismEq : MotiveMorphismEqualityTarget C)
    (framedOf : {X Y : C} → (X ⟶ Y) → SomeFramedPeriodDatum ctx)
    (comparisonOf : {X Y : C} → (X ⟶ Y) → SomeStructuredComparisonMorphism ctx) where
  scalarShadowLevel : ∀ {X Y : C}, (X ⟶ Y) → (X ⟶ Y) → Prop
  framedLevel : ∀ {X Y : C}, (X ⟶ Y) → (X ⟶ Y) → Prop
  structuredLevel : ∀ {X Y : C}, (X ⟶ Y) → (X ⟶ Y) → Prop
  morphismLevel : ∀ {X Y : C}, (X ⟶ Y) → (X ⟶ Y) → Prop

/-- The scalar shadow appearing in the final target is the actual shadow of the packed
comparison datum. -/
structure ScalarShadowSoundness
    (C : Type u) [Category.{v} C]
    (ctx : ClassicalComparisonContext.{w, x})
    (comparisonOf : {X Y : C} → (X ⟶ Y) → SomeStructuredComparisonMorphism ctx)
    (shadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx))
    (shadowOf : {X Y : C} → (X ⟶ Y) → shadow.ScalarCarrier) where
  theoremTarget :
    ∀ {X Y : C} (f : X ⟶ Y),
      shadowOf f = shadow.shadowOf (comparisonOf f)

/-- The framed shadow appearing in the framed lane is the actual shadow of the framed witness. -/
structure FramedShadowSoundness
    (C : Type u) [Category.{v} C]
    (ctx : ClassicalComparisonContext.{w, x})
    (framedOf : {X Y : C} → (X ⟶ Y) → SomeFramedPeriodDatum ctx)
    (shadow : ScalarPeriodShadow (SomeFramedPeriodDatum ctx))
    (shadowOf : {X Y : C} → (X ⟶ Y) → shadow.ScalarCarrier) where
  theoremTarget :
    ∀ {X Y : C} (f : X ⟶ Y),
      shadowOf f = shadow.shadowOf (framedOf f)

/-- Compatibility theorem target comparing the framed shadow with the scalar shadow of the packed
structured comparison datum. -/
structure FramedToScalarCompatibility
    (C : Type u) [Category.{v} C]
    (ctx : ClassicalComparisonContext.{w, x})
    (framedOf : {X Y : C} → (X ⟶ Y) → SomeFramedPeriodDatum ctx)
    (comparisonOf : {X Y : C} → (X ⟶ Y) → SomeStructuredComparisonMorphism ctx)
    (framedShadow : ScalarPeriodShadow (SomeFramedPeriodDatum ctx))
    (scalarShadow : ScalarPeriodShadow (SomeStructuredComparisonMorphism ctx))
    (toScalar : framedShadow.ScalarCarrier → scalarShadow.ScalarCarrier) where
  theoremTarget :
    ∀ {X Y : C} (f : X ⟶ Y),
      scalarShadow.equalityRelation
        (scalarShadow.shadowOf (comparisonOf f))
        (toScalar (framedShadow.shadowOf (framedOf f)))

/-- Structured comparison equality reflects motive-morphism equality. -/
structure StructuredComparisonFaithfulness
    (C : Type u) [Category.{v} C]
    (ctx : ClassicalComparisonContext.{w, x})
    (structuredEq : StructuredComparisonEquality ctx)
    (comparisonOf : {X Y : C} → (X ⟶ Y) → SomeStructuredComparisonMorphism ctx)
    (morphismEq : MotiveMorphismEqualityTarget C) where
  theoremTarget :
    ∀ {X Y : C} (f g : X ⟶ Y),
      structuredEq.relates (comparisonOf f) (comparisonOf g) →
        morphismEq.relates f g

/-- Manuscript-facing name for the faithfulness step above the reflection core. -/
abbrev StructuredComparisonFaithfulnessCore := StructuredComparisonFaithfulness

end ClassicalPeriods
end TraceCalc
