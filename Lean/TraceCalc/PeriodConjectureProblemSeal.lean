import TraceCalc.LayerD.ConcretePeriodFaithfulness
import TraceCalc.ClassicalPeriods.PeriodConjectureTarget
import TraceCalc.MotivicRecognition.ManuscriptSpineTargets

universe u v w x y z

namespace TraceCalc
namespace PeriodConjectureProblemSeal

open ClassicalPeriods

/-!
# Period Conjecture Problem Seal

This module is an audit-only seal exposing the exact theorem surfaces used for
classical period-faithfulness conclusions.

It adds no assumptions, no new axioms, and no wrapper relations. Its role is to
make theorem types visibly checkable for mathematical audit.

## Theorem shape invariants

- Left side hypotheses are scalar/basis-free period equalities (`f.basisFreePeriodMap = g.basisFreePeriodMap`).
- Right side conclusion is literal morphism equality (`f = g`) when using the combined theorem.
- No `EqMorph` wrapper is used in the concrete theorem aliases here.
- No `PeriodFaithfulnessContext` hypothesis is used in these aliases.
- No `PLift True` or `EqMorph := True` context is involved in this seal.

## Grep audit instructions (run from repository root)

Check for vacuous wrappers and forbidden patterns:
```
rg -n "EqMorph.*True|PLift True|ScalarShadow.*True|StructuredRealization.*True|sorry|admit|axiom|by trivial" \
  Lean/TraceCalc --glob '!**/LayerG/Mock*'
```

Check for spurious period-quotient equality:
```
rg -n "Setoid|Quotient|Equiv|Eq" Lean/TraceCalc | rg "period|Period|basisFree"
```

Check that ScalarShadow does not carry witnesses, traces, or reconstruction certificates:
```
rg -n "ScalarShadow|scalar.*witness|scalar.*certificate|scalar.*trace|scalar.*reconstruction|scalar.*comparisonIso" \
  Lean/TraceCalc
```
-/

/-! ## Concrete theorem shape aliases

These `def`s spell out the Prop shape of the two direct concrete theorems.
They are definitionally equal to the bodies of the originals and introduce
no new universe or structure overhead. -/

/-- Exact shape of the direct over-scalar reflection theorem.

**Hypothesis**: equality of basis-free period maps (`f.basisFreePeriodMap = g.basisFreePeriodMap`).
**Conclusion**: equality of the two over-scalar realization maps (deRham and Betti). -/
def ClassicalScalarPeriodFaithfulnessStatement : Prop :=
  ∀ {ctx : ClassicalComparisonContext.{u, v}}
    (source target : ClassicalStructuredComparisonObject.{u, v, w, x, y, z} ctx)
    (f g : ClassicalStructuredComparisonMorphism source target),
    f.basisFreePeriodMap = g.basisFreePeriodMap →
      f.deRhamMapOverScalar = g.deRhamMapOverScalar ∧
      f.bettiMapOverScalar = g.bettiMapOverScalar

/-- Exact shape of the concrete literal-equality theorem.

**Hypotheses**: base-level Betti/de Rham map equalities together with
  scalar/basis-free period map equality.
**Conclusion**: literal morphism equality `f = g`.
No `EqMorph` wrapper. No `PeriodFaithfulnessContext` hypothesis. -/
def ClassicalFullMorphismEqualityFromBasisFreeStatement : Prop :=
  ∀ {ctx : ClassicalComparisonContext.{u, v}}
    {source target : ClassicalStructuredComparisonObject.{u, v, w, x, y, z} ctx}
    (f g : ClassicalStructuredComparisonMorphism source target),
    f.bettiMap = g.bettiMap →
    f.deRhamMap = g.deRhamMap →
    f.basisFreePeriodMap = g.basisFreePeriodMap →
    f = g

/-! ## Theorem aliases

These are `theorem` definitions that re-state and prove the concrete theorems
by direct application, confirming that the originals have exactly these types. -/

/-- Alias to the concrete over-scalar reflection theorem.
Proves the shape alias `ClassicalScalarPeriodFaithfulnessStatement` from
`LayerD.scalar_period_faithfulness_classical`. -/
theorem scalar_period_faithfulness_classical_sealed :
    ClassicalScalarPeriodFaithfulnessStatement.{u, v} :=
  fun source target f g h =>
    LayerD.scalar_period_faithfulness_classical source target f g h

/-- Alias to the concrete literal-equality theorem.
Proves the shape alias `ClassicalFullMorphismEqualityFromBasisFreeStatement` from
`LayerD.full_morphism_eq_of_basisFreePeriodMap_eq`. -/
theorem full_morphism_eq_of_basisFreePeriodMap_eq_sealed :
    ClassicalFullMorphismEqualityFromBasisFreeStatement.{u, v} :=
  fun f g hBetti hDeRham hBasis =>
    LayerD.full_morphism_eq_of_basisFreePeriodMap_eq f g hBetti hDeRham hBasis

/-- Final period-conjecture theorem endpoint currently exposed in production.
This takes a `BaseFaithfulnessTarget` package and returns its `faithfulnessStatement`. -/
theorem baseFaithfulness_of_reflection_sealed
    (target : PeriodConjectureTargetIndex.BaseFaithfulnessTarget.{u, v, w}) :
    target.faithfulnessStatement :=
  PeriodConjectureTargetIndex.baseFaithfulness_of_reflection target

/-- Final framed period-conjecture theorem endpoint currently exposed in production.
This takes a `FramedFaithfulnessTarget` package and returns its `faithfulnessStatement`. -/
theorem framedFaithfulness_of_reflection_sealed
    (target : PeriodConjectureTargetIndex.FramedFaithfulnessTarget.{u, v, w}) :
    target.faithfulnessStatement :=
  PeriodConjectureTargetIndex.framedFaithfulness_of_reflection target

/-! ## #check probes

These expose the precise Lean-elaborated type of each theorem for human inspection. -/

#check LayerD.scalar_period_faithfulness_classical
#check LayerD.full_morphism_eq_of_basisFreePeriodMap_eq
#check PeriodConjectureTargetIndex.baseFaithfulness_of_reflection
#check PeriodConjectureTargetIndex.framedFaithfulness_of_reflection
#check MotivicRecognition.ProofRelevantPeriodTheoremTarget
#check ClassicalScalarPeriodFaithfulnessStatement
#check ClassicalFullMorphismEqualityFromBasisFreeStatement

/-! ## #print axioms

Confirms that the two concrete theorems depend only on `propext` and `Quot.sound`,
with no `sorry`, no `Classical.choice` escape, and no custom axioms. -/

#print axioms LayerD.scalar_period_faithfulness_classical
#print axioms LayerD.full_morphism_eq_of_basisFreePeriodMap_eq

end PeriodConjectureProblemSeal
end TraceCalc
