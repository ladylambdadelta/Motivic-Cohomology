import TraceCalc.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.LayerD.ConcretePeriodFaithfulness

/-!
# Package 8A: Injective-extension period faithfulness provider

This file seals the injective-extension sub-packet of the full period faithfulness
theorem route.  It does NOT seal full Package 8 (which requires `bettiAgreementTarget`,
`deRhamAgreementTarget`, `periodMatrixAgreementTarget` from `RealizationComparisonTarget`
— those have no proof source yet).

## What is sealed here

Three concrete faithfulness theorems, all proved from first principles:

1. `scalar_period_faithfulness_via_injective_extensions_bridge`
   — equal basis-free period maps imply equality of the over-scalar realization maps.
   Proved from `ClassicalStructuredComparisonMorphism.deRhamMapOverScalar_eq_of_basisFreePeriodMap_eq`
   and `bettiMapOverScalar_eq_of_basisFreePeriodMap_eq` in ClassicalPeriods.Basic.

2. `internal_period_faithfulness_of_injective_extensions_bridge`
   — equal basis-free period maps imply full morphism equality, given that the
   target object's extension maps `extendBetti` and `extendDeRham` are injective.
   Proved via the over-scalar route and the extension-compatibility squares.
   Conditional on: `Function.Injective target.extendBetti`,
                   `Function.Injective target.extendDeRham`.

3. `legacyComparisonFaithfulnessInput_from_injective_extensions`
  — the old conditional injective-extension statement, retained for legacy callers after
  the final P8 surface moved to realization-agreement inputs.

## What is NOT sealed here

- `proofRelevantPeriodStatementTarget` (needs `canonicalEquivalenceTarget`
  and `homotopyCategoryComparisonTarget`, both blocked on P6).
- `bettiAgreementTarget`, `deRhamAgreementTarget`, `comparisonIsomorphismAgreementTarget`,
  `periodMatrixAgreementTarget` in `RealizationComparisonTarget` — no proof source yet.

## Provider record

`InjectiveExtensionPeriodFaithfulnessProvider ctx` collects precisely the provable
obligations as named proof-carrying fields.  It does not include any field that
requires unsatisfied upstream packages.

## Remaining Package 8 blockers

- `bettiAgreementTarget` : requires Betti realization functor + comparison.
- `deRhamAgreementTarget` : requires de Rham realization functor + comparison.
- `comparisonIsomorphismAgreementTarget` : requires comparison isomorphism transport.
- `periodMatrixAgreementTarget` : requires explicit period-matrix computation.
- `proofRelevantPeriodStatementTarget` : blocked on P6 (canonical DM_gm(Q) equivalence).
-/

namespace TraceCalc.MotivicRecognition

universe u v w x y z

open ClassicalPeriods
open LayerD
open LayerB.RealObjects.RewriteCalculusSetup

/-! ## Named bridge theorems -/

/-- **Bridge theorem 1** (scalar level, unconditional).

Equal basis-free period maps imply equality of both over-scalar realization maps.

This is a named alias for `LayerD.scalar_period_faithfulness_classical` that makes
the bridge to the `ProofRelevantPeriodTheoremTarget` route explicit.

Axioms: [propext, Quot.sound]. No extra hypotheses. -/
theorem scalar_period_faithfulness_via_injective_extensions_bridge
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : ClassicalStructuredComparisonObject ctx)
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap) :
    f.deRhamMapOverScalar = g.deRhamMapOverScalar ∧
    f.bettiMapOverScalar = g.bettiMapOverScalar :=
  LayerD.scalar_period_faithfulness_classical source target f g hBasis

/-- **Bridge theorem 2** (full morphism level, conditional on injectivity).

Equal basis-free period maps imply full morphism equality, given that the
target object's extension maps are injective.

Proof route:
  basis-free period equality
  →  (via `scalar_period_faithfulness_classical`) over-scalar map equality
  →  (via extension-compatibility squares + `Function.Injective` hypotheses) full map equality
  →  (via `ClassicalStructuredComparisonMorphism.eq_of_map_fields_eq`) morphism equality.

Hypotheses that remain explicit:
  `hExtendBettiInj` : `Function.Injective target.extendBetti`
  `hExtendDeRhamInj` : `Function.Injective target.extendDeRham`
These are genuine mathematical conditions; they are NOT discharged in this file.

Axioms: [propext, Quot.sound]. -/
theorem internal_period_faithfulness_of_injective_extensions_bridge
    {ctx : ClassicalComparisonContext.{u, v}}
    (source target : ClassicalStructuredComparisonObject ctx)
    (f g : ClassicalStructuredComparisonMorphism source target)
    (hExtendBettiInj : Function.Injective target.extendBetti)
    (hExtendDeRhamInj : Function.Injective target.extendDeRham)
    (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap) :
    f = g :=
  LayerD.internal_period_faithfulness_of_injective_extensions
    source target f g hExtendBettiInj hExtendDeRhamInj hBasis

/-- **Bridge theorem 3**: the exact `comparisonFaithfulnessInputTarget` shape.

This is the old conditional statement formerly stored by
`ProofRelevantPeriodTheoremTarget.comparisonFaithfulnessInputTarget`. It is sealed here as a named theorem, bridging from
`internal_period_faithfulness_of_injective_extensions_bridge`.

The theorem is universally quantified over source and target comparison objects,
over pairs of morphisms, and over the two injectivity hypotheses — matching the
stored `∀`-quantification in `ProofRelevantPeriodTheoremTarget`.

Axioms: [propext, Quot.sound]. -/
theorem legacyComparisonFaithfulnessInput_from_injective_extensions
    {ctx : ClassicalComparisonContext.{u, v}} :
    ∀ (source target : ClassicalStructuredComparisonObject ctx)
      (f g : ClassicalStructuredComparisonMorphism source target),
      Function.Injective target.extendBetti →
      Function.Injective target.extendDeRham →
      f.basisFreePeriodMap = g.basisFreePeriodMap →
      f = g :=
  fun source target f g hBettiInj hDeRhamInj hBasis =>
    internal_period_faithfulness_of_injective_extensions_bridge
      source target f g hBettiInj hDeRhamInj hBasis

/-! ## Provider structure -/

/-- **Injective-extension period faithfulness provider** for context `ctx`.

This structure collects exactly the provable obligations from the injective-extension
route.  Each field has a literal proof term; no field is set to `True` or proved by
`trivial`.

Fields:
- `scalarFaithfulness_holds`: over-scalar realization maps agree when basis-free
  period maps agree (unconditional).
- `morphismEqOfInjectiveExtensions_holds`: full morphism equality from basis-free
  period equality, given target-extension injectivity (explicit hypotheses kept).
- `legacyComparisonFaithfulnessInput_holds`: the old conditional injective-extension
  quantified statement retained for legacy callers.

Explicit REMAINING hypotheses carried by this provider:
- Injectivity of `target.extendBetti` — condition on source data.
- Injectivity of `target.extendDeRham` — condition on source data.
These are NOT pretended to be discharged. -/
structure InjectiveExtensionPeriodFaithfulnessProvider
    (ctx : ClassicalComparisonContext.{u, v}) where
  /-- Over-scalar faithfulness: equal basis-free period maps → equal over-scalar maps.
  Proved unconditionally from `scalar_period_faithfulness_classical`. -/
  scalarFaithfulness_holds :
    ∀ (source target : ClassicalStructuredComparisonObject ctx)
      (f g : ClassicalStructuredComparisonMorphism source target),
      f.basisFreePeriodMap = g.basisFreePeriodMap →
      f.deRhamMapOverScalar = g.deRhamMapOverScalar ∧ f.bettiMapOverScalar = g.bettiMapOverScalar
  /-- Full morphism equality from basis-free period equality, conditional on
  target-extension injectivity (explicit hypotheses retained). -/
  morphismEqOfInjectiveExtensions_holds :
    ∀ (source target : ClassicalStructuredComparisonObject ctx)
      (f g : ClassicalStructuredComparisonMorphism source target),
      Function.Injective target.extendBetti →
      Function.Injective target.extendDeRham →
      f.basisFreePeriodMap = g.basisFreePeriodMap →
      f = g
  /-- Legacy conditional comparison-faithfulness input, proved from the
  injective-extension route. -/
  legacyComparisonFaithfulnessInput_holds :
    ∀ (source target : ClassicalStructuredComparisonObject ctx)
      (f g : ClassicalStructuredComparisonMorphism source target),
      Function.Injective target.extendBetti →
      Function.Injective target.extendDeRham →
      f.basisFreePeriodMap = g.basisFreePeriodMap →
      f = g

/-! ## Provider constructor -/

namespace PeriodFaithfulnessProvider

/-- **Sealed provider**: construct `InjectiveExtensionPeriodFaithfulnessProvider ctx`
from the three bridge theorems proved in this file.

This is the axiom-receipt entry point for Package 8A.  All three fields are filled
by named theorems; no field is `True` or `trivial`.

Remaining Package 8 blockers (not in this provider):
- `bettiAgreementTarget`, `deRhamAgreementTarget`, `comparisonIsomorphismAgreementTarget`,
  `periodMatrixAgreementTarget` in `RealizationComparisonTarget`.
- `proofRelevantPeriodStatementTarget` blocked on P6. -/
def ofInjectiveExtensions
    (ctx : ClassicalComparisonContext.{u, v}) :
    InjectiveExtensionPeriodFaithfulnessProvider ctx where
  scalarFaithfulness_holds :=
    scalar_period_faithfulness_via_injective_extensions_bridge
  morphismEqOfInjectiveExtensions_holds :=
    internal_period_faithfulness_of_injective_extensions_bridge
  legacyComparisonFaithfulnessInput_holds :=
    legacyComparisonFaithfulnessInput_from_injective_extensions

end PeriodFaithfulnessProvider

end TraceCalc.MotivicRecognition
