import TraceCalc.ClassicalPeriods.GeometricObjects
import TraceCalc.ClassicalPeriods.AlgebraicCycleCategory
import TraceCalc.ClassicalPeriods.Package3B0ConcreteCycles
import TraceCalc.ClassicalPeriods.Package3B0VoevodskyFiniteCorrespondences

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods

namespace Package3B0

/-- A finite correspondence between two geometric period objects.

In the Voevodsky-Suslin category Cor(Sm/k):
  - Objects:   smooth k-varieties X
  - Mor(X, Y): free abelian group on integral closed Z ⊂ X × Y,
               finite and surjective over connected components of X
  - Identity:  the diagonal Δ_X ⊂ X × X  (graph of id_X)
  - Composition: β ∘ α = (p₁₃)_*( (p₁₂)^* α ∩ (p₂₃)^* β )

For the categorical-laws proof we reuse the nontrivial quotient skeleton from
`Package3B0ConcreteCycles`: a raw integer-multiplicity correspondence model
quotiented by actual equality of multiplicity data.  This still abstracts away
the full geometry, but it no longer collapses correspondence structure to a
singleton witness.
-/
def FiniteCorrespondence
    {ctx : ClassicalComparisonContext.{u, v}}
    (_source _target : GeometricPeriodObject ctx) : Type :=
  VoevodskyFiniteCorrespondences.FiniteCorrespondence

namespace FiniteCorrespondence

/-- Identity correspondence: the diagonal Δ_X ⊂ X × X. -/
def identityCorrespondence
    {ctx : ClassicalComparisonContext.{u, v}}
    (X : GeometricPeriodObject ctx) :
    FiniteCorrespondence X X :=
  VoevodskyFiniteCorrespondences.identityCorrespondence

/-- Composition of correspondences.

Given α : X ⇝ Y and β : Y ⇝ Z, the composite β ∘ α is defined as
  β ∘ α = (p₁₃)_*( (p₁₂)^* α · (p₂₃)^* β )
in the X × Y × Z product.  Here we reuse the quotient-multiplicity skeleton
from `Package3B0ConcreteCycles`. -/
def composeCorrespondence
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y Z : GeometricPeriodObject ctx}
    (_α : FiniteCorrespondence X Y)
    (_β : FiniteCorrespondence Y Z) :
    FiniteCorrespondence X Z :=
  VoevodskyFiniteCorrespondences.composeCorrespondence _α _β

end FiniteCorrespondence

namespace FiniteCorrespondenceBridge

/-- Left identity: id ∘ α = α.

In the Voevodsky-Suslin theory this holds because composing with Δ_X
on the left recovers α by the projection formula for the graph of id_X.
Here it is inherited from the quotient-multiplicity skeleton.
-/
theorem finiteCorrespondence_id_left_from_cycles
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : GeometricPeriodObject ctx}
    (α : FiniteCorrespondence X Y) :
    FiniteCorrespondence.composeCorrespondence
      (FiniteCorrespondence.identityCorrespondence X) α = α :=
  VoevodskyFiniteCorrespondences.finiteCorrespondence_id_left α

/-- Right identity: α ∘ id = α. -/
theorem finiteCorrespondence_id_right_from_cycles
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : GeometricPeriodObject ctx}
    (α : FiniteCorrespondence X Y) :
    FiniteCorrespondence.composeCorrespondence α
      (FiniteCorrespondence.identityCorrespondence Y) = α :=
  VoevodskyFiniteCorrespondences.finiteCorrespondence_id_right α

/-- Associativity: (α ∘ β) ∘ γ = α ∘ (β ∘ γ).

In the Voevodsky-Suslin theory this follows from functoriality of
pushforward-pullback-intersection and the projection formula on fiber
products.  Here it is inherited from the quotient-multiplicity skeleton.
-/
theorem finiteCorrespondence_assoc_from_cycles
    {ctx : ClassicalComparisonContext.{u, v}}
    {W X Y Z : GeometricPeriodObject ctx}
    (α : FiniteCorrespondence W X)
    (β : FiniteCorrespondence X Y)
    (γ : FiniteCorrespondence Y Z) :
    FiniteCorrespondence.composeCorrespondence
      (FiniteCorrespondence.composeCorrespondence α β) γ =
    FiniteCorrespondence.composeCorrespondence α
      (FiniteCorrespondence.composeCorrespondence β γ) :=
  VoevodskyFiniteCorrespondences.finiteCorrespondence_assoc α β γ

end FiniteCorrespondenceBridge

/-- Left identity law: id ∘ α = α.

Proved from the concrete quotient-multiplicity correspondence layer.
-/
theorem finiteCorrespondence_id_left
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : GeometricPeriodObject ctx}
    (α : FiniteCorrespondence X Y) :
    FiniteCorrespondence.composeCorrespondence
      (FiniteCorrespondence.identityCorrespondence X) α = α :=
  FiniteCorrespondenceBridge.finiteCorrespondence_id_left_from_cycles α

/-- Right identity law: α ∘ id = α. -/
theorem finiteCorrespondence_id_right
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : GeometricPeriodObject ctx}
    (α : FiniteCorrespondence X Y) :
    FiniteCorrespondence.composeCorrespondence α
      (FiniteCorrespondence.identityCorrespondence Y) = α :=
  FiniteCorrespondenceBridge.finiteCorrespondence_id_right_from_cycles α

/-- Associativity law: (α ∘ β) ∘ γ = α ∘ (β ∘ γ). -/
theorem finiteCorrespondence_assoc
    {ctx : ClassicalComparisonContext.{u, v}}
    {W X Y Z : GeometricPeriodObject ctx}
    (α : FiniteCorrespondence W X)
    (β : FiniteCorrespondence X Y)
    (γ : FiniteCorrespondence Y Z) :
    FiniteCorrespondence.composeCorrespondence
      (FiniteCorrespondence.composeCorrespondence α β) γ =
    FiniteCorrespondence.composeCorrespondence α
      (FiniteCorrespondence.composeCorrespondence β γ) :=
  FiniteCorrespondenceBridge.finiteCorrespondence_assoc_from_cycles α β γ

end Package3B0

end ClassicalPeriods
end TraceCalc
