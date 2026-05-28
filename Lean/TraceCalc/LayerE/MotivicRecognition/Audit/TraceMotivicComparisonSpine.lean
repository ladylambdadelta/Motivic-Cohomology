import TraceCalc.LayerB.RealObjects.PeelChain
import TraceCalc.LayerB.RealObjects.Replay
import TraceCalc.LayerB.RealObjects.Unpeel
import TraceCalc.LayerB.RealObjects.SwapSquare
import TraceCalc.LayerB.RealObjects.CanonicalReconstructionEngine
import TraceCalc.LayerB.RealObjects.SyntacticHolography
import TraceCalc.LayerB.RealObjects.ResidueCanNF
import TraceCalc.LayerBNonCore.Contracts.CanNFObligations
import TraceCalc.LayerB.RealObjects.CanNFProductionSystem
import TraceCalc.LayerD.ConcretePeriodFaithfulness
import TraceCalc.LayerE.MotivicRecognition.ManuscriptSpineTargets

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

open LayerB.RealObjects
open LayerD
open ClassicalPeriods
open LayerB.RealObjects.RewriteCalculusSetup
open CompletedReconstructionRecord
open CompletedReconstructionRecord.PeelChain
open PeelChain

/-!
# Status

Future theorem ledger / audit summary.

This file is not imported by the public period-conjecture proof route. It is
kept because it names and packages a stronger assembled proof program for later
normalization/recognition cleanup, rather than because it participates in the
current exported theorem boundary.

# Trace-to-motivic comparison spine: assembled proof route

This module assembles the central paper proof route from the now-classified components.

The spine represents the actual TeX proof chain:
1. **T_raw → Tcan**: trace reconstruction (sink peeling, completeness, termination)
2. **Tcan → CanNF**: canonical normal form rewrite system (confluence, well-definedness)
3. **CanNF → holography**: syntactic boundary holography (conditional on presentation)
4. **Period faithfulness**: internal period comparison (weaker than paper; needs extra field hyps)
5. **DM_gm(Q) recognition**: trace-to-motivic-increments bridge (support structure)
6. **Classical comparison**: period theorem route (conditional on prerequisites)

Each spine structure documents:
- The TeX reference (manuscript label and line)
- The paper's mathematical role
- The Lean proof status and source (proved, conditional, or support)
- Why any gap exists between the paper claim and what Lean currently proves

The spine records consumed proofs and required obligations without adding fake
wrappers, sorry's, or trivial placeholders.
-/

/-! ## Part 1: Trace reconstruction spine -/

/-- **Trace reconstruction backbone**: completes the TeX §2-§4 proof chain
from certified raw trace (T_raw) to canonical completed trace (Tcan).

This spine packages the four reconstruction theorems: termination (the sink-peel
descent is well-founded), existence (every completed record admits a canonical peel chain),
uniqueness (all peel chains replay equivalently), and retraction (replay inverts peel).

All four are genuine paper theorem proofs with no gap.
-/
structure TraceReconstructionSpine
    {setup : RewriteCalculusSetup.{u}} where

  /-
  TEX ref: our_paper_draft.tex, label prop:reconstruction-termination (L1165+)
  Paper role: the canonical reconstruction algorithm terminates on every
    completed record, proved by well-founded induction on R.n
  Lean status: PROVED-PAPER
  Proof source: PeelChain.canonicalPeelChain_completes (proved in file)
  -/
  /-- The canonical reconstruction algorithm terminates for every completed record. -/
  termination :
    ∀ (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted),
      ∃ (c : PeelChain R), c.Completes :=
    @reconstruction_termination setup

  /-
  TEX ref: our_paper_draft.tex, label prop:reconstruction-existence (L1172+)
  Paper role: for every completed record there exists a canonical completed trace;
    the reconstruction algorithm produces such a trace
  Lean status: PROVED-PAPER
  Proof source: PeelChain.canonicalPeelChain + PeelChain.canonicalPeelChain_completes
    + PeelChain.canonicalPeelChain_isCanonical (proved in file)
  -/
  /-- Every completed record admits a canonical peel-chain reconstruction
  that both completes and is canonical. -/
  existence :
    ∀ (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted),
      ∃ (c : PeelChain R), c.Completes ∧ c.IsCanonical :=
    @reconstruction_existence setup

  /-
  TEX ref: our_paper_draft.tex, label prop:reconstruction-uniqueness (L1178+)
  Paper role: any two peel chains over the same record produce replay results
    that are record-equivalent (administratively identical)
  Lean status: PROVED-PAPER
  Proof source: Replay.replay_stable (proved in file; named alias reconstruction_uniqueness)
  -/
  /-- Any two peel chains over the same record replay to administratively
  equivalent results. The reconstruction is canonical up to admin equivalence. -/
  uniqueness :
    ∀ {R : CompletedReconstructionRecord setup}
      (c c' : PeelChain R),
      RecordEquiv (replay c) (replay c') :=
    @reconstruction_uniqueness setup

  /-
  TEX ref: our_paper_draft.tex, label cor:reconstruction-retraction (L1182+)
  Paper role: the replay of any peel chain is record-equivalent to the original
    (replay is a retraction / inverse of peel)
  Lean status: PROVED-PAPER
  Proof source: Replay.replay_recordEquiv (proved in file; named alias reconstruction_retraction)
  -/
  /-- Replay of any peel chain returns a record equivalent to the original,
  proving that the peel-reconstruction cycle is a retraction. -/
  retraction :
    ∀ {R : CompletedReconstructionRecord setup}
      (c : PeelChain R),
      RecordEquiv (replay c) R :=
    @reconstruction_retraction setup

  /-
  TEX ref: our_paper_draft.tex, label lem:sink-deletion-inverse (L1160+)
  Paper role: peeling a sink and then unpeeling is the identity up to
    record equivalence; the sink-peel operation is invertible
  Lean status: PROVED-PAPER
  Proof source: Unpeel.unpeelSink_peelSink (proved in file; named alias sink_deletion_inverse)
  -/
  /-- Peeling a sink and unpeeling the result is record-equivalent to the identity.
  The sink-peel operation is invertible modulo administrative equivalence. -/
  sink_deletion_inverse :
    ∀ (R : CompletedReconstructionRecord setup) (s : Fin R.n) (hSink : R.IsSink s),
      RecordEquiv (unpeelSink (peelSink R s) (sinkData R s)) R :=
    @sink_deletion_inverse setup


/-! ## Part 2: CanNF normalization spine -/

/-- **Canonical normal form rewrite spine**: packages the CanNF algorithm layer,
convergence, and well-definedness (TeX §5-6).

This spine documents the condition under which the CanNF system converges and
produces unique normal forms. The normalization completeness field projects an
obligation from CanNFObligations, and the well-definedness field projects from
ResidueCanNFContract.

Both are conditional on their respective contract fields being discharged.
-/
structure CanNFNormalizationSpine
    {setup : RewriteCalculusSetup.{u}} where

  /-
  TEX ref: our_paper_draft.tex, label prop:local-confluence (L1380+)
  Paper role: the CanNF rewrite system satisfies local confluence
    (diamond / Church-Rosser property)
  Lean status: CONDITIONAL — proved from `CanonicalFrontierReductionSystem.canonical_local_diamond`
    given a `CanonicalFrontierReductionSystem` instance. The single remaining gap
    is `CanonicalFrontierReductionSystem.canonical_step_joinability`: the named
    one-step Church-Rosser obligation for the concrete system.
  Proof source: CanonicalFrontierReductionSystem.canonical_local_diamond
    (which uses local_diamond_from_join_cases + frontier_join_cases_of_step_joinability)
  -/
  /-- The CanNF rewrite system satisfies local confluence: any two divergent
  single steps can be rejoined via multi-step reductions.

  This is now wired through the **concrete named system**
  `CanonicalFrontierReductionSystem C`: given any instance of the named
  concrete system (which bundles a `FrontierReductionSystem`, a
  `classify_pair` function, and the named `canonical_step_joinability`
  obligation), local confluence follows unconditionally via
  `canonical_local_diamond`.

  The sole remaining gap is discharging
  `CanonicalFrontierReductionSystem.canonical_step_joinability` for a
  specific concrete reduction system — this requires operational semantics
  for each residue-level rule family (not yet available). -/
  local_confluence_obligation :
    (C : CanonicalFrontierReductionSystem setup) →
      ∀ (w w₁ w₂ : FrontierWord setup),
        C.reductionSystem.Step w w₁ →
        C.reductionSystem.Step w w₂ →
          ∃ w' : FrontierWord setup,
            C.reductionSystem.MultiStep w₁ w' ∧
            C.reductionSystem.MultiStep w₂ w' :=
    fun C w w₁ w₂ h₁ h₂ =>
      CanonicalFrontierReductionSystem.canonical_local_diamond C h₁ h₂

  /-- Production-local-confluence route through the concrete production
  assembly (`ProductionSchemaOperationalSpec` + split critical-pair data). -/
  production_local_confluence_conditional :
    (spec : ProductionSchemaOperationalSpec setup) →
    (CP : ProductionCriticalPairSplitData (productionFrontierRuleSystem_from_spec spec)) →
      ∀ (w w₁ w₂ : FrontierWord setup),
        (productionFrontierReductionSystem_from_spec spec).Step w w₁ →
        (productionFrontierReductionSystem_from_spec spec).Step w w₂ →
          ∃ w' : FrontierWord setup,
            (productionFrontierReductionSystem_from_spec spec).MultiStep w₁ w' ∧
            (productionFrontierReductionSystem_from_spec spec).MultiStep w₂ w' :=
    fun spec CP w w₁ w₂ h₁ h₂ =>
      production_cannf_local_confluence_from_spec spec CP h₁ h₂

  /-
  TEX ref: our_paper_draft.tex, label thm:normalization-completeness (L1404+)
  Paper role: canonical normal form normalization is complete:
    two words have the same normal form iff they are frontier-word equivalent
  Lean status: CONDITIONAL-FIELD-PROJECTION (not proved from first principles)
  Proof source: Projects CanNFObligations.complete field
    (CanNFObligations.normalization_completeness_from_obligations)
  Gap: the actual manuscript proof (that completeness follows from the rewrite
    system properties) remains in the CanNFObligations.complete obligation.
    The Lean declaration only unpacks this field.
  -/
  /-- Normalization completeness: two words have the same normal form iff they
  are frontier-word equivalent. This is conditional on the CanNFObligations.complete
  field providing the actual completeness proof. -/
  normalization_completeness_conditional :
    {NF : Type v} → {normalize : FrontierWord setup → NF} →
    (O : CanNFObligations setup NF normalize) →
    ∀ {w₁ w₂ : FrontierWord setup},
      normalize w₁ = normalize w₂ → FrontierWord.Equiv w₁ w₂ :=
    fun {NF normalize} O {w₁ w₂} h => normalization_completeness_from_obligations O h

  /-
  TEX ref: our_paper_draft.tex, label prop:canNF-well-defined (L1408+)
  Paper role: the canonical normal form is well-defined: does not depend
    on the representative chosen in an equivalence class
  Lean status: CONDITIONAL-FIELD-PROJECTION (not proved from first principles)
  Proof source: Projects ResidueCanNFContract.sound and .complete fields
    (ResidueCanNF.canNF_well_defined_from_contract)
  Gap: the proof only assembles the contract's sound and complete fields;
    the actual algebraic verification remains in those fields.
  -/
  /-- Well-definedness of CanNF: two equivalent words have equal normal forms
  and conversely. Conditional on the ResidueCanNFContract contract providing
  the actual sound/complete proofs. -/
  canNF_well_defined_conditional :
    {O : ResidueCanonicalOrder.{u, v} setup} →
    (C : ResidueCanNFContract O) →
    ∀ (w₁ w₂ : FrontierWord setup),
      (C.normalize w₁).word = (C.normalize w₂).word ↔ FrontierWord.Equiv w₁ w₂ :=
    fun {O} C w₁ w₂ => canNF_well_defined_from_contract C w₁ w₂

  /-- Production-contract wording for normalization completeness. -/
  production_normalization_completeness_conditional :
    (C : ProductionCanNFContract setup) →
    ∀ {w₁ w₂ : FrontierWord setup},
      C.normalize w₁ = C.normalize w₂ → FrontierWord.Equiv w₁ w₂ :=
    fun C {w₁} {w₂} h => production_normalization_completeness C h

  /-- Production-contract wording for CanNF well-definedness. -/
  production_canNF_well_defined_conditional :
    (C : ProductionCanNFContract setup) →
    ∀ (w₁ w₂ : FrontierWord setup),
      (C.residueContract.normalize w₁).word
        = (C.residueContract.normalize w₂).word ↔ FrontierWord.Equiv w₁ w₂ :=
    fun C w₁ w₂ => production_canNF_well_defined C w₁ w₂

  /-
  TEX ref: our_paper_draft.tex, label prop:canNF-church-rosser (constructive route)
  Paper role: the `buildNormalizerFn` normalizer satisfies sound_compat (equiv inputs
    → same normal-form word) via confluence + Church-Rosser bridge.
  Lean status: PROVED-CONSTRUCTIVE-PRODUCTION conditional on `JP` + `CR`
    — `JP` supplies concrete critical-pair joinability (local confluence data);
    — `CR` (FrontierWordChurchRosserData) supplies the completeness bridge:
         every FrontierWord.Equiv-related pair can be joined by multi-step reductions.
  Proof source: productionCanNFObligations_from_church_rosser
    (which uses ProductionCanNFSoundCompatData.from_church_rosser + Newman's lemma)
  -/
  /-- Constructive production CanNF obligations:
  `buildNormalizerFn` as the normalizer, with `sound_compat` proved constructively
  via confluence (Newman's lemma) and the `FrontierWordChurchRosserData` bridge.

  Conditional on:
  * `spec : ProductionSchemaOperationalSpec` (production system spec)
  * `JP  : ProductionJoinEnvPrimitive`       (concrete joinability data for Newman)
  * `CR  : FrontierWordChurchRosserData`     (completeness bridge: Equiv → zigzag) -/
  production_canNF_obligations_from_church_rosser :
    (spec : ProductionSchemaOperationalSpec setup) →
    (JP : ProductionJoinEnvPrimitive (productionFrontierRuleSystem_from_spec spec)) →
    (CR : FrontierWordChurchRosserData (productionFrontierReductionSystem_from_spec spec)) →
      CanNFObligations setup (FrontierWord setup)
        (fun w => (FrontierReductionSystem.buildNormalizerFn
                     (productionFrontierReductionSystem_from_spec spec) w).nf_word) :=
    fun spec JP CR => productionCanNFObligations_from_church_rosser spec JP CR

  /-
  TEX ref: our_paper_draft.tex, label prop:canNF-church-rosser (half-decomposition route)
  Paper role: Church-Rosser seam reduced to two named half-obligations:
    (A) Y-only zigzag (boundary_admin_canonicalize family)
    (B) externalOut-only zigzag (expose_boundary_block_swap family)
  Lean status: PROVED-CONSTRUCTIVE-PRODUCTION conditional on `JP` + `BA` + `EO`

  As of 2026-04-27: BOTH HALVES ARE NOW PROVED given concrete data:
    — `BA` : filled by `CanNFProductionBoundaryAdminChurchRosserData.from_concrete`
             given BC (BoundaryAdminCanonicalizeCongr) + TC + KC
    — `EO` : filled by `CanNFProductionExternalOutChurchRosserData.from_sort_data`
             given TC + KC + EOSort (CanNFProductionExternalOutSortData)

  Remaining named obligations (5 total):
    — JP     : ProductionJoinEnvPrimitive (1 Prop field: join_all_non_disjoint)
    — BC     : BoundaryAdminCanonicalizeCongr (1 Prop: canonicalizeY_congr) ← NEXT TARGET
    — TC     : TensorFactorOrderCanonicalizeUniqueData (1 Prop: canonicalizeTensor_unique)
    — KC     : KeyOrderCanonicalizeUniqueData (1 Prop: canonicalizeKey_unique)
    — EOSort : CanNFProductionExternalOutSortData (3 fields incl. reduce_to_fully_canonical)

  Proof source: FrontierWordChurchRosserData.from_production_halves
    (decomposition via w_mid + confluence (Newman + JP))
  Full concrete route: productionCanNFObligations_from_concrete_data (JP+BC+TC+KC+EOSort)
  -/
  /-- Constructive production CanNF obligations via the two-halves decomposition:
  reduces `FrontierWordChurchRosserData` to the two named half-obligations `BA`
  (Y-only) and `EO` (externalOut-only), assembled by Newman's lemma.

  Both halves can now be filled from concrete data:
  * `BA` via `CanNFProductionBoundaryAdminChurchRosserData.from_concrete` (BC + TC + KC)
  * `EO` via `CanNFProductionExternalOutChurchRosserData.from_sort_data` (TC + KC + EOSort)

  Use `productionCanNFObligations_from_concrete_data` for the fully concrete route. -/
  production_canNF_obligations_from_production_halves :
    (spec : ProductionSchemaOperationalSpec setup) →
    (JP : ProductionJoinEnvPrimitive (productionFrontierRuleSystem_from_spec spec)) →
    (BA : CanNFProductionBoundaryAdminChurchRosserData spec) →
    (EO : CanNFProductionExternalOutChurchRosserData spec) →
      CanNFObligations setup (FrontierWord setup)
        (fun w => (FrontierReductionSystem.buildNormalizerFn
                     (productionFrontierReductionSystem_from_spec spec) w).nf_word) :=
    fun spec JP BA EO =>
      productionCanNFObligations_from_production_halves spec JP BA EO


/-! ## Part 3: Tensor factor independence and swap square -/

/-- **Tensor factor independence spine**: the reconstruction of a tensor-factored
record is independent of the order in which sink factors are peeled (TeX §4).

The spine documents the swap-square property (proved from admin equivalence) and
the full tensor independence claim (remaining as obligation).
-/
structure TensorFactorIndependenceSpine
    {setup : RewriteCalculusSetup.{u}} where

  /-
  TEX ref: our_paper_draft.tex, label thm:tensor-factor-independence (L1168+)
  Paper role: the canonical reconstruction of a record with multiple tensor
    factors is independent of the order in which those factors' sinks are peeled
  Lean status: PROVED-SUPPORT (partial proof of swap-square only)
  Proof source: SwapSquare.tensorFactorIndependence_swap_square_holds_proof
    (proves via peelSink_swap_structEquiv_admin)
  Gap: only the swap-square half is proved. The full TensorFactorIndependence
    includes a second obligation field (tensor_reconstruction_independence) that
    remains unverified.
  -/
  /-- Swap-square property: peeling independent sinks s and t in either order
  yields admin-equivalent results. This half of tensor-factor independence is
  proved from admin equivalence. The full independence (including tensor-product
  reconstruction) remains an open obligation. -/
  swap_square_half :
    ∀ {R : CompletedReconstructionRecord setup} {s t : Fin R.n}
      (h : IndependentSinks R s t),
      RecordStructEquiv (@BoundaryAdminEquiv setup)
        (peelSink (peelSink R s) (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)))
        (peelSink (peelSink R t) (peelSinkOtherIdx t s h.s_ne_t)) :=
    by
      intro R s t h
      exact tensorFactorIndependence_swap_square_holds_proof setup h

  /-
  The full tensor-factor independence theorem includes an additional obligation:
  that the reconstruction of a tensor product factors canonically through the
  component reconstructions. This field is present in SwapSquare.TensorFactorIndependence
  but remains unverified.
  -/
  /-- Full tensor-factor independence remains an obligation structure field. -/
  tensor_reconstruction_independence_obligation :
    (T : TensorFactorIndependence setup) →
      T.tensor_reconstruction_independence


/-! ## Part 4: Holography conditional support -/

/-- **Holography conditional spine**: the holographic reconstruction condition
(TeX §4 remark on completeness and holography).

The holography support is proved conditionally on a syntactic boundary
presentation existing.
-/
structure HolographyConditionalSpine
    {setup : RewriteCalculusSetup.{u}} where

  /-
  TEX ref: our_paper_draft.tex, label rem:infty-holography (L1084+)
  Paper role: remark claiming completed-level / ∞-holography of the
    reconstruction algorithm
  Lean status: PROVED-SUPPORT (conditional on SyntacticBoundaryPresentation)
  Proof source: SyntacticHolography.syntactic_boundary_holographic_reconstruction
    (proved in file; named alias infty_holography_conditional_support_note_holds)
  Gap: the paper claims unconditional completed holography. The Lean proof is
    conditional on providing a SyntacticBoundaryPresentation: the holography
    equivalence only holds given an explicit boundary presentation and its
    quotient realization.
  -/
  /-- Holographic reconstruction: under a syntactic boundary presentation,
  the holographic quotient realization detects frontier-word equivalence.
  This is conditional on the presentation hypothesis; the paper's claim of
  unconditional completed holography remains open. -/
  holography_under_presentation :
    ∀ (P : SyntacticBoundaryPresentation setup)
      (D : HolographicReconstructionData setup)
      {R₁ R₂ : CompletedReconstructionRecord setup},
      (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
        (D.toFrontierWord R₁) =
      (syntactic_boundary_presentation_gives_holographic_quotient_realization P).realize
        (D.toFrontierWord R₂) ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂) :=
    by
      intro P D R₁ R₂
      exact infty_holography_conditional_support_note_holds


/-! ## Part 5: Period faithfulness comparison -/

/-- **Internal period faithfulness spine**: the comparison between basis-free
period data and structured comparison morphisms (TeX §10).

The spine documents the actual Lean proof, which requires 4 extra field hypotheses
beyond what the paper needs. The 4 extra hypotheses are: bettiMap, deRhamMap,
bettiExtensionCompatibility, deRhamExtensionCompatibility equality hypotheses.
-/
structure PeriodFaithfulnessSpine
    {ctx : ClassicalComparisonContext.{u, v}} where

  /-
  TEX ref: our_paper_draft.tex, label cor:internal-period-faithfulness (L700+)
  Paper role: equal basis-free period maps imply equal structured comparison
    morphisms (period faithfulness corollary)
  Lean status: PROVED-WEAKER
  Proof source: ConcretePeriodFaithfulness.full_morphism_eq_of_betti_deRham_basisFreePeriodMap_eq
    (renamed alias: internal_period_faithfulness_weaker)
  Gap: the paper claims this follows from the comparison constraint alone.
    The Lean proof requires 4 additional field hypotheses:
    - bettiMap equality (hBetti)
    - deRhamMap equality (hDeRham)
    - bettiExtensionCompatibility equality (hBettiComp)
    - deRhamExtensionCompatibility equality (hDeRhamComp)
    The paper's proof strategy for deriving these 4 equalities from the
    comparison constraint is not yet formalized.
  -/
  /-- Period faithfulness with 4 extra field hypotheses (PROVED-WEAKER).
  Equal basis-free periods and equal structured field data implies equal morphisms.
  The 4 extra hypotheses represent the gap between the paper's claim (unconditional)
  and the current Lean proof (conditional on field equality). -/
  period_faithfulness_with_field_data :
    ∀ (source target : ClassicalStructuredComparisonObject ctx)
      (f g : ClassicalStructuredComparisonMorphism source target),
      f.basisFreePeriodMap = g.basisFreePeriodMap →
      f.bettiMap = g.bettiMap →
      f.deRhamMap = g.deRhamMap →
      f.bettiExtensionCompatibility = g.bettiExtensionCompatibility →
      f.deRhamExtensionCompatibility = g.deRhamExtensionCompatibility →
      f = g :=
    internal_period_faithfulness_weaker

  /-
  TEX ref: our_paper_draft.tex, label cor:internal-period-faithfulness (L700+)
  Paper role: equal basis-free period maps imply equal structured comparison
    morphisms, given that target extension maps are injective (PROVED-STRONGER)
  Lean status: PROVED-STRONGER
  Proof source: ConcretePeriodFaithfulness.internal_period_faithfulness_of_injective_extensions
  Gap closure: replaces the 4 extra field-equality hypotheses of the PROVED-WEAKER
    version with 2 injectivity conditions on the target's extension maps
    (extendBetti and extendDeRham). This partially closes obligation 4 from
    AssembledPaperSpine: field gap closure via target-level injectivity.
  -/
  /-- Period faithfulness via injectivity of target extension maps (PROVED-STRONGER).
  Equal basis-free period maps imply equal morphisms when the target object's
  extension maps `extendBetti` and `extendDeRham` are injective.
  Consumes `ConcretePeriodFaithfulness.internal_period_faithfulness_of_injective_extensions`.
  This reduces the 4 extra field-equality hypotheses to 2 injectivity conditions. -/
  period_faithfulness_of_injective_extensions :
    ∀ (source target : ClassicalStructuredComparisonObject ctx)
      (f g : ClassicalStructuredComparisonMorphism source target),
      Function.Injective target.extendBetti →
      Function.Injective target.extendDeRham →
      f.basisFreePeriodMap = g.basisFreePeriodMap →
      f = g :=
    internal_period_faithfulness_of_injective_extensions


/-! ## Part 6: Reconstruction support and algorithm packaging -/

/-- **Canonical reconstruction algorithm support spine**: packages the proof
that a CanonicalReconstructionEngine instance exists (TeX §4, thm:canonical-reconstruction-algorithm).

The support structure demonstrates that the reconstruction *infrastructure* can be
instantiated, but does not close the full theorem as stated in the paper. The full
theorem requires: termination, existence, uniqueness, and tensor-factor independence,
four of which have been moved to separate spines above (three as PROVED-PAPER,
one as OBLIGATION-STRUCTURE).
-/
structure ReconstructionAlgorithmSupportSpine
    {setup : RewriteCalculusSetup.{u}} where

  /-
  TEX ref: our_paper_draft.tex, label thm:canonical-reconstruction-algorithm (L859+)
  Paper role: the canonical reconstruction algorithm theorem at manuscript level
  Lean status: PROVED-SUPPORT (partial: Nonempty of engine structure only)
  Proof source: CanonicalReconstructionEngine.ofClosedCanNF
    (proved via canonical_reconstruction_algorithm_support_boundary_holds)
  Gap: proves the packaging structure can be instantiated by a concrete
    `CanonicalReconstructionEngine setup`. The paper's full theorem statement
    requires all four reconstruction obligations (termination, existence,
    uniqueness, tensor independence) to be discharged. Three are PROVED-PAPER
    (termination, existence, uniqueness). One (tensor independence) remains
    an OBLIGATION-STRUCTURE.
  -/
  /-- Support: a concrete `CanonicalReconstructionEngine` instance.
  This constructs the packaging structure itself, but does not close the full
  manuscript theorem (which requires 4 sub-theorems including tensor independence). -/
  engine : CanonicalReconstructionEngine setup :=
    (CanonicalReconstructionEngine.ofClosedCanNF (setup := setup) :
      CanonicalReconstructionEngine setup)

namespace ReconstructionAlgorithmSupportSpine

/-- Package any concrete reconstruction engine as the support spine's
existence witness. -/
def ofEngine
    {setup : RewriteCalculusSetup.{u}}
    (eng : CanonicalReconstructionEngine setup) :
    ReconstructionAlgorithmSupportSpine (setup := setup) where
  engine := eng

/-- Semantic bridge constructor matching the default support witness. -/
noncomputable def ofClosedCanNF
    {setup : RewriteCalculusSetup.{u}} :
    ReconstructionAlgorithmSupportSpine (setup := setup) :=
  ofEngine (CanonicalReconstructionEngine.ofClosedCanNF (setup := setup))

/-- Computational bridge constructor lifting an executable CanNF normalizer
through the support spine. -/
noncomputable def ofComputationalCanNF
    {setup : RewriteCalculusSetup.{u}}
    (N : ComputationalFrontierNormalizer setup) :
    ReconstructionAlgorithmSupportSpine (setup := setup) :=
  ofEngine (CanonicalReconstructionEngine.ofComputationalCanNF N)

end ReconstructionAlgorithmSupportSpine


/-! ## Part 7: Full paper assembly obligations -/

/-- **Full paper assembly obligations**: the top-level record collecting all
remaining obligations needed to close the manuscript proof spine.

This structure documents:
- The 4 fully proved reconstruction claims (termination, existence, uniqueness, retraction)
- The 3 proved-but-conditional claims (swap-square, holography, period faithfulness weaker)
- The 2 conditional field projections (completeness, well-definedness)
- The remaining open mathematical obligations needed to bridge to the full paper span
-/
structure FullPaperAssemblyObligations
    {setup : RewriteCalculusSetup.{u}}
    {ctx : ClassicalComparisonContext.{u, v}} where

  /-- The trace reconstruction theorems (all PROVED-PAPER). -/
  reconstruction : TraceReconstructionSpine (setup := setup)

  /-- The CanNF normalization spine (confluence, completeness, well-definedness).
  Completeness and well-definedness are conditional on contracts. -/
  normalization : CanNFNormalizationSpine (setup := setup)

  /-- The swap-square property (PROVED-SUPPORT; full tensor independence is obligation). -/
  tensor_independence : TensorFactorIndependenceSpine (setup := setup)

  /-- Holography conditional on presentation (PROVED-SUPPORT). -/
  holography : HolographyConditionalSpine (setup := setup)

  /-- Period faithfulness with field data gap (PROVED-WEAKER). -/
  period_faithfulness : PeriodFaithfulnessSpine (ctx := ctx)

  /-- Reconstruction algorithm packaging support (PROVED-SUPPORT). -/
  algorithm_support : ReconstructionAlgorithmSupportSpine (setup := setup)


/-! ## Part 8: Assembled paper spine -/

/-- **Central assembled paper spine**: the complete representation of the TeX
proof route using proved, conditional, and support declarations.

This record witnesses that 5 PROVED-PAPER theorems are closed, 3 PROVED-SUPPORT
theorems provide partial closure, 1 PROVED-WEAKER theorem admits a gap, and
2 CONDITIONAL-FIELD-PROJECTION theorems depend on contract fields.

Remaining major proof obligations:
1. **Join lemmas** (lem:join-corr-corr, lem:join-corr-loc, etc.) —
   confluence witnesses for the CanNF rewrite system.
2. **Tensor reconstruction independence** — the full tensor-factor-independence
   second obligation (only swap-square is proved).
3. **Dependent graph acyclicity from completeness** —
   the connection between IsCompleted structure and acyclic dependency.
4. **Field gap closure for period faithfulness** — deriving 4 field equalities
   from the comparison constraint alone. PARTIAL: `internal_period_faithfulness_of_injective_extensions`
   closes this when target extension maps are injective (2 injectivity hypotheses
   replace 4 field-equality hypotheses). Full unconditional closure still missing.
5. **Holography unconditional** — removing the syntactic boundary presentation
   hypothesis and proving completed ∞-holography directly.
6. **Classical coarse period consequence** — integrating period faithfulness
   with tomography and period pairings (4 prerequisites MISSING).
-/
structure AssembledPaperSpine
    {setup : RewriteCalculusSetup.{u}}
    {ctx : ClassicalComparisonContext.{u, v}} where

  /-- The full assembly of proved and conditional components. -/
  assembly : FullPaperAssemblyObligations (setup := setup) (ctx := ctx)

  /-
  Supporting claims and notes on the assembly.
  -/

  /-- **PROVED-PAPER declarations consumed**: 5
  - reconstruction_termination (prop:reconstruction-termination)
  - reconstruction_existence (prop:reconstruction-existence)
  - reconstruction_uniqueness (prop:reconstruction-uniqueness)
  - reconstruction_retraction (cor:reconstruction-retraction)
  - sink_deletion_inverse (lem:sink-deletion-inverse)
  -/
  paper_proofs_count : ℕ := 5

  /-- **PROVED-SUPPORT declarations consumed**: 3
  - `Nonempty` engine witness via `CanonicalReconstructionEngine.ofClosedCanNF`
  - infty_holography_conditional_support_note_holds
  - tensorFactorIndependence_swap_square_holds_proof
  Each proves a partial aspect or requires a hypothesis not claimed by the paper.
  -/
  support_proofs_count : ℕ := 3

  /-- **PROVED-WEAKER declarations consumed**: 1
  - internal_period_faithfulness_weaker (4 extra field hypotheses)
  -/
  weaker_proofs_count : ℕ := 1

  /-- **PROVED-STRONGER declarations consumed**: 1
  - internal_period_faithfulness_of_injective_extensions
    (replaces 4 field-equality hypotheses with 2 injectivity conditions;
     partial closure of obligation 4: field gap closure for period faithfulness)
  -/
  stronger_proofs_count : ℕ := 1

  /-- **CONDITIONAL-FIELD-PROJECTION declarations consumed**: 2
  - normalization_completeness_from_obligations (projects O.complete)
  - canNF_well_defined_from_contract (projects C.sound and C.complete)
  These only unpack contract fields, not proved from first principles.
  -/
  conditional_projections_count : ℕ := 2

/- **Central assembled paper spine definition**: The paper proof route can be
assembled from the classified components in this module and upstream modules.

An instance of AssembledPaperSpine is constructed by collecting:
- The 4 PROVED-PAPER reconstruction theorems
- The 3 PROVED-SUPPORT boundary-crossing claims
- The 1 PROVED-WEAKER period faithfulness with field gap
- The 2 CONDITIONAL-FIELD-PROJECTION contract unpacking declarations

This records the current state of the paper proof: 5 claims closed, 3 partial,
1 weaker, 2 conditional, and several obligations remaining (join lemmas,
tensor independence, field equalities, holography unconditional, period consequence). -/

/-! ## Production system local confluence bridge -/

/-- **`production_local_confluence_obligation`**: from a
`ProductionReductionSystemData` instance, obtain local confluence for
the production CanNF system.

This is the **full wiring** connecting `ProductionReductionSystemData`
(= `FrontierRuleSystem` + `ResidueRewriteCommutes` + `CriticalPairResolved`)
to `prop:local-confluence` via
`theorem_production_cannf_local_diamond`.

The two obligation structure fields of `O` (`ResidueRewriteCommutes` and
`CriticalPairResolved`) are the precise remaining gaps between the current
state and a fully operational CanNF implementation. -/
theorem production_local_confluence_obligation
    {setup : RewriteCalculusSetup.{u}}
    (O : ProductionReductionSystemData setup)
    {w w₁ w₂ : FrontierWord setup}
    (h₁ : O.ruleSystem.toFrontierReductionSystem.Step w w₁)
    (h₂ : O.ruleSystem.toFrontierReductionSystem.Step w w₂) :
    ∃ w' : FrontierWord setup,
      O.ruleSystem.toFrontierReductionSystem.MultiStep w₁ w' ∧
      O.ruleSystem.toFrontierReductionSystem.MultiStep w₂ w' :=
  theorem_production_cannf_local_diamond O h₁ h₂

end MotivicRecognition
end TraceCalc
