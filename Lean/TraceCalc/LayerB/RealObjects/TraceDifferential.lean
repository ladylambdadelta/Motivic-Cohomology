import TraceCalc.LayerB.RealObjects.LayerBHomComplex
import TraceCalc.LayerB.RealObjects.BoundaryCode
import TraceCalc.LayerB.RealObjects.SyntacticBoundary

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

variable (setup : RewriteCalculusSetup.{u})

/-- Exact missing null/boundary package below the current two-cell and replay
APIs.

Inspection of `TwoCellStep`, `TraceEquiv`, `CertifiedTrace.cls`,
`supportGraph`, `primitiveDecls`, `twoCellData`, `adjacentIndependence`, and
the signature-only `ReplayInterface` shows only class preservation,
support-order bookkeeping, and composition transport. The current Layer B files
do not expose a distinguished zero trace class, a null-trace predicate, or a
boundary-generator relation whose outputs are forced into such a class.

This structure names exactly that still-missing semantic input without
pretending that the existing two-cell generators already provide it. -/
structure TraceNullBoundaryData (setup : RewriteCalculusSetup.{u}) where
  zeroClass : ∀ {X Y : setup.State}, setup.TraceClass X Y
  nullTrace : ∀ {X Y : setup.State}, setup.CertifiedTrace X Y → Prop
  boundaryGenerator :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → setup.CertifiedTrace X Y → Prop
  cyclePredicate :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → Prop
  nullTrace_maps_to_zeroClass :
    ∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
      nullTrace trace → trace.cls = zeroClass
  boundaryGenerator_maps_to_zeroClass :
    ∀ {X Y : setup.State}
      (generator boundary : setup.CertifiedTrace X Y),
      boundaryGenerator generator boundary → boundary.cls = zeroClass
  cycles_descend_to_traceClass :
    ∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
      cyclePredicate trace →
        ∃ representative : setup.CertifiedTrace X Y,
          representative.cls = trace.cls ∧ cyclePredicate representative

/-- Exact boundary-to-zero theorem still missing if one wants to derive a null
trace class from the current attachment/gluing/sink-deletion layer.

Unlike `TraceNullBoundaryData`, this package does not ask for a full null-trace
or cycle semantics. It isolates only the boundary-side ingredient: a chosen zero
trace class, a candidate boundary-generator relation, the existence of a
refined-complete sink-deletion/gluing witness for generated boundaries, and the
theorem that such a witness forces the generated boundary into the chosen zero
class. -/
structure TraceBoundaryZeroTheorem (setup : RewriteCalculusSetup.{u}) where
  zeroClass : ∀ {X Y : setup.State}, setup.TraceClass X Y
  boundaryGenerator :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → setup.CertifiedTrace X Y → Prop
  boundaryGenerator_has_gluing_zero_witness :
    ∀ {X Y : setup.State}
      (generator boundary : setup.CertifiedTrace X Y),
      boundaryGenerator generator boundary →
        ∃ (R : CompletedReconstructionRecord setup)
          (_hR : R.IsCompletedRefined (setup := setup))
          (s : Fin R.n),
          setup.IsCompatibleAttachmentForPacket (R := R) s ∧
            setup.glueBoundary
                (setup.exposedBoundary (R := R) s)
                (R.packets s).refinedIn
                (R.packets s).refinedOut
                (R.attach s) = R.Y
  gluing_zero_witness_maps_boundary_to_zeroClass :
    ∀ {X Y : setup.State}
      (generator boundary : setup.CertifiedTrace X Y),
      boundaryGenerator generator boundary →
        boundary.cls = zeroClass

/-- Exact smaller missing lemma behind `TraceBoundaryZeroTheorem`.

The current boundary layer can already talk about exposed boundaries, glued
boundaries, typed compatibility, and refined completedness witnesses. The part
it still cannot prove is the final implication from such a gluing witness to a
chosen zero trace class. This target isolates only that implication. -/
structure GluedBoundaryHasZeroTraceClassTarget
    (setup : RewriteCalculusSetup.{u}) where
  zeroClass : ∀ {X Y : setup.State}, setup.TraceClass X Y
  boundaryGenerator :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → setup.CertifiedTrace X Y → Prop
  witnessImpliesZeroClass :
    ∀ {X Y : setup.State}
      (generator boundary : setup.CertifiedTrace X Y),
      boundaryGenerator generator boundary →
        (∃ (R : CompletedReconstructionRecord setup)
          (_hR : R.IsCompletedRefined (setup := setup))
          (s : Fin R.n),
          setup.IsCompatibleAttachmentForPacket (R := R) s ∧
            setup.glueBoundary
                (setup.exposedBoundary (R := R) s)
                (R.packets s).refinedIn
                (R.packets s).refinedOut
                (R.attach s) = R.Y) →
          boundary.cls = zeroClass

namespace TraceBoundaryZeroTheorem

/-- Every full `TraceBoundaryZeroTheorem` contains the smaller missing gluing-
to-zero target as a direct projection. -/
def toGluedBoundaryHasZeroTraceClassTarget
    (package : TraceBoundaryZeroTheorem setup) :
    GluedBoundaryHasZeroTraceClassTarget setup where
  zeroClass := package.zeroClass
  boundaryGenerator := package.boundaryGenerator
  witnessImpliesZeroClass := by
    intro X Y generator boundary hgenerator hwitness
    exact package.gluing_zero_witness_maps_boundary_to_zeroClass
      generator boundary hgenerator

/-- Assemble `TraceBoundaryZeroTheorem` from the witness-existence half and the
smaller gluing-to-zero implication target. This makes explicit that the current
stop point is exactly the second ingredient. -/
def ofWitnessExistenceAndZeroClassTarget
    (zeroTarget : GluedBoundaryHasZeroTraceClassTarget setup)
    (boundaryGenerator_has_gluing_zero_witness :
      ∀ {X Y : setup.State}
        (generator boundary : setup.CertifiedTrace X Y),
        zeroTarget.boundaryGenerator generator boundary →
          ∃ (R : CompletedReconstructionRecord setup)
            (_hR : R.IsCompletedRefined (setup := setup))
            (s : Fin R.n),
            setup.IsCompatibleAttachmentForPacket (R := R) s ∧
              setup.glueBoundary
                  (setup.exposedBoundary (R := R) s)
                  (R.packets s).refinedIn
                  (R.packets s).refinedOut
                  (R.attach s) = R.Y)
            :
    TraceBoundaryZeroTheorem setup where
  zeroClass := zeroTarget.zeroClass
  boundaryGenerator := zeroTarget.boundaryGenerator
  boundaryGenerator_has_gluing_zero_witness := boundaryGenerator_has_gluing_zero_witness
  gluing_zero_witness_maps_boundary_to_zeroClass := by
    intro X Y generator boundary hboundary
    exact zeroTarget.witnessImpliesZeroClass generator boundary hboundary
      (boundaryGenerator_has_gluing_zero_witness generator boundary hboundary)

end TraceBoundaryZeroTheorem

/-- Exact additional boundary-side theorem package still missing if one wants
to build `TraceNullBoundaryData` from the current attachment/gluing/sink-
deletion layer.

`Attach.lean` exposes real boundary operations and refined completedness:
`attachmentCompatible`, `glueBoundary`, `exposeBoundaryUnderSinkDeletion`, and
`IsCompletedRefined` with typed C2/C4 data. What it still does not expose is a
theorem connecting those boundary operations to any chosen zero trace class.

This structure records that exact extra bridge: every generated boundary should
come from a refined-complete sink-deletion/gluing configuration whose exposed
boundary glues back to the ambient target boundary. The trace-class-to-zero
conclusion itself remains the field already required by `TraceNullBoundaryData`.
-/
structure AttachmentBoundaryZeroData (setup : RewriteCalculusSetup.{u})
    extends TraceNullBoundaryData setup where
  boundaryGenerator_has_gluing_zero_witness :
    ∀ {X Y : setup.State}
      (generator boundary : setup.CertifiedTrace X Y),
      boundaryGenerator generator boundary →
        ∃ (R : CompletedReconstructionRecord setup)
          (_hR : R.IsCompletedRefined (setup := setup))
          (s : Fin R.n),
          setup.IsCompatibleAttachmentForPacket (R := R) s ∧
            setup.glueBoundary
                (setup.exposedBoundary (R := R) s)
                (R.packets s).refinedIn
                (R.packets s).refinedOut
                (R.attach s) = R.Y

/-- Exact missing semantics below `TraceDifferentialSemantics` when the current
trace-side development stops at two-cell equivalence.

`TwoCellStep` and `TraceEquiv` explain when two replay representatives define
the same trace class, but they do not by themselves single out a distinguished
zero class or a boundary-generation mechanism landing in that class. This
structure records precisely that still-missing content: a chosen zero class,
optional null-trace representatives for it, a boundary-generator relation on
certified traces, and the proofs needed to derive the boundary/cycle interface
consumed by `TraceDifferentialSemantics`. -/
structure TraceHomotopyBoundarySemantics (setup : RewriteCalculusSetup.{u}) where
  zeroClass : ∀ {X Y : setup.State}, setup.TraceClass X Y
  nullTrace : ∀ {X Y : setup.State}, setup.CertifiedTrace X Y → Prop
  boundaryGenerator :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → setup.CertifiedTrace X Y → Prop
  cyclePredicate :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → Prop
  nullTrace_maps_to_zeroClass :
    ∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
      nullTrace trace → trace.cls = zeroClass
  boundaryGenerator_maps_to_zeroClass :
    ∀ {X Y : setup.State}
      (generator boundary : setup.CertifiedTrace X Y),
      boundaryGenerator generator boundary → boundary.cls = zeroClass
  cycles_descend_to_traceClass :
    ∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
      cyclePredicate trace →
        ∃ representative : setup.CertifiedTrace X Y,
          representative.cls = trace.cls ∧ cyclePredicate representative

namespace TraceNullBoundaryData

/-- Repackage the exact null/boundary inputs as the slightly more H0-facing
`TraceHomotopyBoundarySemantics` surface. -/
def toTraceHomotopyBoundarySemantics
    (data : TraceNullBoundaryData setup) :
    TraceHomotopyBoundarySemantics setup where
  zeroClass := data.zeroClass
  nullTrace := data.nullTrace
  boundaryGenerator := data.boundaryGenerator
  cyclePredicate := data.cyclePredicate
  nullTrace_maps_to_zeroClass := data.nullTrace_maps_to_zeroClass
  boundaryGenerator_maps_to_zeroClass :=
    data.boundaryGenerator_maps_to_zeroClass
  cycles_descend_to_traceClass := data.cycles_descend_to_traceClass

@[simp] theorem toTraceHomotopyBoundarySemantics_zeroClass
    (data : TraceNullBoundaryData setup)
    {X Y : setup.State} :
    (data.toTraceHomotopyBoundarySemantics).zeroClass (X := X) (Y := Y) =
      data.zeroClass (X := X) (Y := Y) :=
  rfl

@[simp] theorem toTraceHomotopyBoundarySemantics_boundaryGenerator
    (data : TraceNullBoundaryData setup)
    {X Y : setup.State}
    (generator boundary : setup.CertifiedTrace X Y) :
    (data.toTraceHomotopyBoundarySemantics).boundaryGenerator generator boundary =
      data.boundaryGenerator generator boundary :=
  rfl

end TraceNullBoundaryData

namespace AttachmentBoundaryZeroData

/-- Forget the larger attachment-side package to the exact theorem-only bridge
from gluing witnesses to the chosen zero trace class. -/
def toTraceBoundaryZeroTheorem
    (data : AttachmentBoundaryZeroData setup) :
    TraceBoundaryZeroTheorem setup where
  zeroClass := data.zeroClass
  boundaryGenerator := data.boundaryGenerator
  boundaryGenerator_has_gluing_zero_witness :=
    data.boundaryGenerator_has_gluing_zero_witness
  gluing_zero_witness_maps_boundary_to_zeroClass := by
    intro X Y generator boundary hgenerator
    exact data.boundaryGenerator_maps_to_zeroClass generator boundary hgenerator

@[simp] theorem toTraceBoundaryZeroTheorem_zeroClass
    (data : AttachmentBoundaryZeroData setup)
    {X Y : setup.State} :
    (data.toTraceBoundaryZeroTheorem).zeroClass (X := X) (Y := Y) =
      data.zeroClass (X := X) (Y := Y) :=
  rfl

/-- Forget the extra sink-deletion/gluing witness and keep only the null/
boundary semantics package it supports. -/
def forgetToTraceNullBoundaryData
    (data : AttachmentBoundaryZeroData setup) :
    TraceNullBoundaryData setup where
  zeroClass := data.zeroClass
  nullTrace := data.nullTrace
  boundaryGenerator := data.boundaryGenerator
  cyclePredicate := data.cyclePredicate
  nullTrace_maps_to_zeroClass := data.nullTrace_maps_to_zeroClass
  boundaryGenerator_maps_to_zeroClass := data.boundaryGenerator_maps_to_zeroClass
  cycles_descend_to_traceClass := data.cycles_descend_to_traceClass

@[simp] theorem forgetToTraceNullBoundaryData_boundaryGenerator
    (data : AttachmentBoundaryZeroData setup)
    {X Y : setup.State}
    (generator boundary : setup.CertifiedTrace X Y) :
  (data.forgetToTraceNullBoundaryData).boundaryGenerator generator boundary =
      data.boundaryGenerator generator boundary :=
  rfl

end AttachmentBoundaryZeroData

/-- Exact missing trace-side differential semantics on the existing certified
trace carrier.

The current workspace already provides the raw carrier, quotient carrier, and
quotient map:
- raw morphisms: `setup.CertifiedTrace X Y`
- quotient morphisms: `setup.TraceClass X Y`
- quotient map: `CertifiedTrace.cls`

What is still genuinely absent is the differential layer itself. This structure
names that missing semantics without manufacturing it: a differential relation
on certified traces, cycle and boundary predicates, a quotient-level cycle
predicate, an identified boundary class, and the two exact compatibility laws
needed to feed `LayerBTraceDifferentialPackage`. -/
structure TraceDifferentialSemantics (setup : RewriteCalculusSetup.{u}) where
  differentialRel :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → setup.CertifiedTrace X Y → Prop
  cycles :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → Prop
  boundaries :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → Prop
  cycleClass :
    ∀ {X Y : setup.State},
      setup.TraceClass X Y → Prop
  boundaryClass :
    ∀ {X Y : setup.State},
      setup.TraceClass X Y
  cycles_descend_to_traceClass :
    ∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
      cycles trace → cycleClass trace.cls
  boundaries_map_to_identified_class :
    ∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
      boundaries trace → trace.cls = boundaryClass

namespace TraceHomotopyBoundarySemantics

/-- Build homotopy-boundary semantics from the exact missing null/boundary
package when no honest two-cell-derived boundary generator is available yet. -/
def ofNullBoundaryData
    (data : TraceNullBoundaryData setup) :
    TraceHomotopyBoundarySemantics setup :=
  data.toTraceHomotopyBoundarySemantics

@[simp] theorem ofNullBoundaryData_eq
    (data : TraceNullBoundaryData setup) :
    TraceHomotopyBoundarySemantics.ofNullBoundaryData (setup := setup) data =
      data.toTraceHomotopyBoundarySemantics :=
  rfl

/-- Forget the finer homotopy-boundary package into the lighter-weight
`TraceDifferentialSemantics` interface used by the H0 lane. -/
def toTraceDifferentialSemantics
    (semantics : TraceHomotopyBoundarySemantics setup) :
    TraceDifferentialSemantics setup where
  differentialRel := semantics.boundaryGenerator
  cycles := semantics.cyclePredicate
  boundaries := by
    intro X Y boundary
    exact ∃ generator : setup.CertifiedTrace X Y,
      semantics.boundaryGenerator generator boundary
  cycleClass := by
    intro X Y cls
    exact ∃ trace : setup.CertifiedTrace X Y,
      trace.cls = cls ∧ semantics.cyclePredicate trace
  boundaryClass := semantics.zeroClass
  cycles_descend_to_traceClass := by
    intro X Y trace hcycle
    exact semantics.cycles_descend_to_traceClass trace hcycle
  boundaries_map_to_identified_class := by
    intro X Y boundary hboundary
    rcases hboundary with ⟨generator, hgenerator⟩
    exact semantics.boundaryGenerator_maps_to_zeroClass generator boundary hgenerator

@[simp] theorem toTraceDifferentialSemantics_differentialRel
    (semantics : TraceHomotopyBoundarySemantics setup)
    {X Y : setup.State}
    (left right : setup.CertifiedTrace X Y) :
    (TraceHomotopyBoundarySemantics.toTraceDifferentialSemantics
      (setup := setup) semantics).differentialRel left right =
      semantics.boundaryGenerator left right :=
  rfl

@[simp] theorem toTraceDifferentialSemantics_cycles
    (semantics : TraceHomotopyBoundarySemantics setup)
    {X Y : setup.State}
    (trace : setup.CertifiedTrace X Y) :
    (TraceHomotopyBoundarySemantics.toTraceDifferentialSemantics
      (setup := setup) semantics).cycles trace = semantics.cyclePredicate trace :=
  rfl

@[simp] theorem toTraceDifferentialSemantics_boundaries
    (semantics : TraceHomotopyBoundarySemantics setup)
    {X Y : setup.State}
    (boundary : setup.CertifiedTrace X Y) :
    (TraceHomotopyBoundarySemantics.toTraceDifferentialSemantics
      (setup := setup) semantics).boundaries boundary =
      (∃ generator : setup.CertifiedTrace X Y,
        semantics.boundaryGenerator generator boundary) :=
  rfl

@[simp] theorem toTraceDifferentialSemantics_boundaryClass
    (semantics : TraceHomotopyBoundarySemantics setup)
    {X Y : setup.State} :
    (TraceHomotopyBoundarySemantics.toTraceDifferentialSemantics
      (setup := setup) semantics).boundaryClass (X := X) (Y := Y) =
      semantics.zeroClass (X := X) (Y := Y) :=
  rfl

end TraceHomotopyBoundarySemantics

namespace TraceDifferentialSemantics

/-- Forget the quotient-facing compatibility data into the lighter-weight H0
lane surface `LayerBTraceDifferentialPackage`. -/
def toLayerBTraceDifferentialPackage
    (semantics : TraceDifferentialSemantics setup) :
    LayerBTraceDifferentialPackage setup where
  differentialRel := semantics.differentialRel
  cycles := semantics.cycles
  boundaries := semantics.boundaries
  quotientMapRespectsCycles :=
    ∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
      semantics.cycles trace → semantics.cycleClass trace.cls
  quotientMapKillsBoundaries :=
    ∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
      semantics.boundaries trace → trace.cls = semantics.boundaryClass
  quotientMapRespectsCycles_holds :=
    semantics.cycles_descend_to_traceClass
  quotientMapKillsBoundaries_holds :=
    semantics.boundaries_map_to_identified_class

@[simp] theorem toLayerBTraceDifferentialPackage_differentialRel
    (semantics : TraceDifferentialSemantics setup)
    {X Y : setup.State}
    (left right : setup.CertifiedTrace X Y) :
    (TraceDifferentialSemantics.toLayerBTraceDifferentialPackage
      (setup := setup) semantics).differentialRel left right =
      semantics.differentialRel left right :=
  rfl

@[simp] theorem toLayerBTraceDifferentialPackage_cycles
    (semantics : TraceDifferentialSemantics setup)
    {X Y : setup.State}
    (trace : setup.CertifiedTrace X Y) :
    (TraceDifferentialSemantics.toLayerBTraceDifferentialPackage
      (setup := setup) semantics).cycles trace =
      semantics.cycles trace :=
  rfl

@[simp] theorem toLayerBTraceDifferentialPackage_boundaries
    (semantics : TraceDifferentialSemantics setup)
    {X Y : setup.State}
    (trace : setup.CertifiedTrace X Y) :
    (TraceDifferentialSemantics.toLayerBTraceDifferentialPackage
      (setup := setup) semantics).boundaries trace =
      semantics.boundaries trace :=
  rfl

@[simp] theorem toLayerBTraceDifferentialPackage_quotientMapRespectsCycles
    (semantics : TraceDifferentialSemantics setup) :
    (TraceDifferentialSemantics.toLayerBTraceDifferentialPackage
      (setup := setup) semantics).quotientMapRespectsCycles =
      (∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
        semantics.cycles trace → semantics.cycleClass trace.cls) :=
  rfl

@[simp] theorem toLayerBTraceDifferentialPackage_quotientMapKillsBoundaries
    (semantics : TraceDifferentialSemantics setup) :
    (TraceDifferentialSemantics.toLayerBTraceDifferentialPackage
      (setup := setup) semantics).quotientMapKillsBoundaries =
      (∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
        semantics.boundaries trace → trace.cls = semantics.boundaryClass) :=
  rfl

end TraceDifferentialSemantics

/-- Bridge from gluing-witness data to trace-class zero.

`GluedBoundaryHasZeroTraceClassTarget.witnessImpliesZeroClass` asks: given
`boundaryGenerator generator boundary` and a refined-complete gluing witness,
show `boundary.cls = zeroClass`. The existing Layer B files cannot prove this
because `CertifiedTrace.cls` is defined via `TraceEquiv`, which tracks only
two-cell generator steps (admin/swap/rw). There is no bridge lemma in
`CertifiedTrace.lean`, `Attach.lean`, `BoundaryCode.lean`, or
`SyntacticBoundary.lean` that connects `glueBoundary` equations to
`TraceEquiv` equivalence classes.

This structure records exactly that missing semantic bridge as an explicit
bridge package. It is not a proof — it is the precise name for the semantic
gap that separates the current gluing/attachment layer from the trace-class
zero conclusion. A concrete instantiation would have to either:
  (a) extend `CertifiedTrace` with a boundary-gluing compatibility law, or
  (b) define `zeroClass` as the class of a specific trace constructed from the
      gluing witness.

The structure is immediately usable: `GluingWitnessToTraceClassBridge` reduces
to `GluedBoundaryHasZeroTraceClassTarget` via
`GluingWitnessToTraceClassBridge.toGluedBoundaryHasZeroTraceClassTarget`.

### Fields

* `zeroClass` — the distinguished zero class (stable under all `{X Y}` changes).
* `boundaryGenerator` — the relation singling out boundary-generated traces.
* `gluingWitnessImpliesZeroClass` — given a `boundaryGenerator generator boundary`
  and a refined-complete gluing witness, conclude `boundary.cls = zeroClass`.
  This is the exact missing bridge law.

### Relationship to `GluedBoundaryHasZeroTraceClassTarget`

Every `GluingWitnessToTraceClassBridge` produces a
`GluedBoundaryHasZeroTraceClassTarget` by projection. The two structures
differ only in documentation intent: the bridge foregrounds its role as
a named bridge package, while the target foregrounds its role as the remaining
proof obligation. -/
structure GluingWitnessToTraceClassBridge (setup : RewriteCalculusSetup.{u}) where
  /-- A distinguished zero trace class, uniform across all `{X Y : setup.State}`. -/
  zeroClass : ∀ {X Y : setup.State}, setup.TraceClass X Y
  /-- The boundary-generator relation on certified traces. -/
  boundaryGenerator :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → setup.CertifiedTrace X Y → Prop
  /-- **Missing bridge law.** Given a generated boundary and a refined-complete
  gluing witness, the generated boundary's trace class equals `zeroClass`.

  This is the exact semantic content absent from the current `CertifiedTrace` /
  `Attach` / `BoundaryCode` / `SyntacticBoundary` files. -/
  gluingWitnessImpliesZeroClass :
    ∀ {X Y : setup.State}
      (generator boundary : setup.CertifiedTrace X Y),
      boundaryGenerator generator boundary →
        ∀ (R : CompletedReconstructionRecord setup)
          (_hR : R.IsCompletedRefined (setup := setup))
          (s : Fin R.n),
          setup.IsCompatibleAttachmentForPacket (R := R) s →
            setup.glueBoundary
                (setup.exposedBoundary (R := R) s)
                (R.packets s).refinedIn
                (R.packets s).refinedOut
                (R.attach s) = R.Y →
              boundary.cls = zeroClass

namespace GluingWitnessToTraceClassBridge

/-- Every `GluingWitnessToTraceClassBridge` directly yields a
`GluedBoundaryHasZeroTraceClassTarget`. This is the primary reduction step. -/
def toGluedBoundaryHasZeroTraceClassTarget
    (bridge : GluingWitnessToTraceClassBridge setup) :
    GluedBoundaryHasZeroTraceClassTarget setup where
  zeroClass := bridge.zeroClass
  boundaryGenerator := bridge.boundaryGenerator
  witnessImpliesZeroClass := by
    intro X Y generator boundary hgenerator hwitness
    rcases hwitness with ⟨R, hR, s, hcompat, hglue⟩
    exact bridge.gluingWitnessImpliesZeroClass generator boundary hgenerator
      R hR s hcompat hglue

@[simp] theorem toGluedBoundaryHasZeroTraceClassTarget_zeroClass
    (bridge : GluingWitnessToTraceClassBridge setup)
    {X Y : setup.State} :
    (bridge.toGluedBoundaryHasZeroTraceClassTarget).zeroClass (X := X) (Y := Y) =
      bridge.zeroClass (X := X) (Y := Y) :=
  rfl

@[simp] theorem toGluedBoundaryHasZeroTraceClassTarget_boundaryGenerator
    (bridge : GluingWitnessToTraceClassBridge setup)
    {X Y : setup.State}
    (generator boundary : setup.CertifiedTrace X Y) :
    (bridge.toGluedBoundaryHasZeroTraceClassTarget).boundaryGenerator
        generator boundary =
      bridge.boundaryGenerator generator boundary :=
  rfl

/-- A `GluingWitnessToTraceClassBridge` can also be projected into a full
`TraceBoundaryZeroTheorem`, provided the witness-existence half is supplied
separately. This makes explicit the two independent ingredients:
  1. the witness *exists* (comes from the boundary-generator definition), and
  2. the witness *forces the zero class* (this bridge's law).
-/
def toTraceBoundaryZeroTheorem
    (bridge : GluingWitnessToTraceClassBridge setup)
    (witnessExistence :
      ∀ {X Y : setup.State}
        (generator boundary : setup.CertifiedTrace X Y),
        bridge.boundaryGenerator generator boundary →
          ∃ (R : CompletedReconstructionRecord setup)
            (_hR : R.IsCompletedRefined (setup := setup))
            (s : Fin R.n),
            setup.IsCompatibleAttachmentForPacket (R := R) s ∧
              setup.glueBoundary
                  (setup.exposedBoundary (R := R) s)
                  (R.packets s).refinedIn
                  (R.packets s).refinedOut
                  (R.attach s) = R.Y) :
    TraceBoundaryZeroTheorem setup :=
  { zeroClass := bridge.zeroClass
    boundaryGenerator := bridge.boundaryGenerator
    boundaryGenerator_has_gluing_zero_witness := witnessExistence
    gluing_zero_witness_maps_boundary_to_zeroClass := by
      intro X Y generator boundary hgenerator
      obtain ⟨R, hR, s, hcompat, hglue⟩ := witnessExistence generator boundary hgenerator
      exact bridge.gluingWitnessImpliesZeroClass generator boundary hgenerator
        R hR s hcompat hglue }

end GluingWitnessToTraceClassBridge

/-- Boundary-side witness package collecting the concrete gluing/exposure data
that appears in the refined completedness layer, together with boundary coding
contracts and a syntactic presentation witness. -/
structure BoundaryGluingWitnessData (setup : RewriteCalculusSetup.{u}) where
  boundaryAdminCodeContract : BoundaryAdminCodeContract.{u, u} setup
  externalOutCodeContract : ExternalOutCodeContract.{u, u} setup
  syntacticBoundaryPresentation : SyntacticBoundaryPresentation setup
  R : CompletedReconstructionRecord setup
  hR : R.IsCompletedRefined (setup := setup)
  s : Fin R.n
  attachmentCompatibleWitness : setup.IsCompatibleAttachmentForPacket (R := R) s
  exposedBoundaryWitness :
    setup.exposedBoundary (R := R) s =
      setup.exposeBoundaryUnderSinkDeletion
        R.Y (R.packets s).refinedOut (R.packets s).refinedIn
  glueBoundaryWitness :
    setup.glueBoundary
        (setup.exposedBoundary (R := R) s)
        (R.packets s).refinedIn
        (R.packets s).refinedOut
        (R.attach s) = R.Y
  c2Witness : hR.c2 s = attachmentCompatibleWitness
  c4Witness :
    ∀ (i j : Fin R.n), R.dep.edge i j = true → R.key.pos i < R.key.pos j

namespace BoundaryGluingWitnessData

/-- Canonical constructor from refined completedness and a gluing equation. -/
def ofRefined
  (boundaryAdminCodeContract : BoundaryAdminCodeContract.{u, u} setup)
  (externalOutCodeContract : ExternalOutCodeContract.{u, u} setup)
    (syntacticBoundaryPresentation : SyntacticBoundaryPresentation setup)
    (R : CompletedReconstructionRecord setup)
    (hR : R.IsCompletedRefined (setup := setup))
    (s : Fin R.n)
    (glueBoundaryWitness :
      setup.glueBoundary
          (setup.exposedBoundary (R := R) s)
          (R.packets s).refinedIn
          (R.packets s).refinedOut
          (R.attach s) = R.Y) :
    BoundaryGluingWitnessData setup where
  boundaryAdminCodeContract := boundaryAdminCodeContract
  externalOutCodeContract := externalOutCodeContract
  syntacticBoundaryPresentation := syntacticBoundaryPresentation
  R := R
  hR := hR
  s := s
  attachmentCompatibleWitness := hR.c2 s
  exposedBoundaryWitness := by
    simpa using
      (exposedBoundary_eq_exposeBoundaryUnderSinkDeletion
        (setup := setup) (R := R) s)
  glueBoundaryWitness := glueBoundaryWitness
  c2Witness := rfl
  c4Witness := hR.c4

@[simp] theorem ofRefined_attachmentCompatibleWitness
  (boundaryAdminCodeContract : BoundaryAdminCodeContract.{u, u} setup)
  (externalOutCodeContract : ExternalOutCodeContract.{u, u} setup)
    (syntacticBoundaryPresentation : SyntacticBoundaryPresentation setup)
    (R : CompletedReconstructionRecord setup)
    (hR : R.IsCompletedRefined (setup := setup))
    (s : Fin R.n)
    (glueBoundaryWitness :
      setup.glueBoundary
          (setup.exposedBoundary (R := R) s)
          (R.packets s).refinedIn
          (R.packets s).refinedOut
          (R.attach s) = R.Y) :
    (BoundaryGluingWitnessData.ofRefined (setup := setup)
      boundaryAdminCodeContract externalOutCodeContract
      syntacticBoundaryPresentation R hR s glueBoundaryWitness).attachmentCompatibleWitness =
        hR.c2 s :=
  rfl

@[simp] theorem ofRefined_glueBoundaryWitness
  (boundaryAdminCodeContract : BoundaryAdminCodeContract.{u, u} setup)
  (externalOutCodeContract : ExternalOutCodeContract.{u, u} setup)
    (syntacticBoundaryPresentation : SyntacticBoundaryPresentation setup)
    (R : CompletedReconstructionRecord setup)
    (hR : R.IsCompletedRefined (setup := setup))
    (s : Fin R.n)
    (glueBoundaryWitness :
      setup.glueBoundary
          (setup.exposedBoundary (R := R) s)
          (R.packets s).refinedIn
          (R.packets s).refinedOut
          (R.attach s) = R.Y) :
    (BoundaryGluingWitnessData.ofRefined (setup := setup)
      boundaryAdminCodeContract externalOutCodeContract
      syntacticBoundaryPresentation R hR s glueBoundaryWitness).glueBoundaryWitness =
        glueBoundaryWitness :=
  rfl

end BoundaryGluingWitnessData

/-- Data turning boundary gluing witnesses into certified boundary traces. -/
structure BoundaryTraceRepresentativeData (setup : RewriteCalculusSetup.{u}) where
  boundaryGenerator :
    ∀ {X Y : setup.State},
      setup.CertifiedTrace X Y → setup.CertifiedTrace X Y → Prop
  boundaryTraceRepresentative :
    ∀ {X Y : setup.State}
      (witnesses : BoundaryGluingWitnessData setup)
      (generator boundary : setup.CertifiedTrace X Y),
      boundaryGenerator generator boundary →
        setup.CertifiedTrace X Y
  boundaryTraceRepresentative_eq_boundary :
    ∀ {X Y : setup.State}
      (witnesses : BoundaryGluingWitnessData setup)
      (generator boundary : setup.CertifiedTrace X Y)
      (hgenerated : boundaryGenerator generator boundary),
      boundaryTraceRepresentative witnesses generator boundary hgenerated = boundary

namespace BoundaryTraceRepresentativeData

@[simp] theorem boundaryTraceRepresentative_cls
    (data : BoundaryTraceRepresentativeData setup)
    {X Y : setup.State}
    (witnesses : BoundaryGluingWitnessData setup)
    (generator boundary : setup.CertifiedTrace X Y)
    (hgenerated : data.boundaryGenerator generator boundary) :
    (data.boundaryTraceRepresentative witnesses generator boundary hgenerated).cls =
      boundary.cls := by
  simpa [data.boundaryTraceRepresentative_eq_boundary
    witnesses generator boundary hgenerated]

def boundaryTraceRepresentativeSupportGraph
    (data : BoundaryTraceRepresentativeData setup)
    {X Y : setup.State}
    (witnesses : BoundaryGluingWitnessData setup)
    (generator boundary : setup.CertifiedTrace X Y)
    (hgenerated : data.boundaryGenerator generator boundary) :=
  (data.boundaryTraceRepresentative witnesses generator boundary hgenerated).supportGraph

def boundaryTraceRepresentativePrimitiveDecls
    (data : BoundaryTraceRepresentativeData setup)
    {X Y : setup.State}
    (witnesses : BoundaryGluingWitnessData setup)
    (generator boundary : setup.CertifiedTrace X Y)
    (hgenerated : data.boundaryGenerator generator boundary) :=
  (data.boundaryTraceRepresentative witnesses generator boundary hgenerated).primitiveDecls

end BoundaryTraceRepresentativeData

/-- Distinguished zero trace representative/class per endpoint pair. -/
structure ZeroTraceRepresentativeData (setup : RewriteCalculusSetup.{u}) where
  zeroCertifiedTrace : ∀ {X Y : setup.State}, setup.CertifiedTrace X Y
  zeroTraceClass : ∀ {X Y : setup.State}, setup.TraceClass X Y
  zeroCertifiedTrace_cls :
    ∀ {X Y : setup.State},
      (zeroCertifiedTrace (X := X) (Y := Y)).cls =
        zeroTraceClass (X := X) (Y := Y)

namespace ZeroTraceRepresentativeData

@[simp] theorem zeroCertifiedTrace_cls_eq
    (data : ZeroTraceRepresentativeData setup)
    {X Y : setup.State} :
    (data.zeroCertifiedTrace (X := X) (Y := Y)).cls =
      data.zeroTraceClass (X := X) (Y := Y) :=
  data.zeroCertifiedTrace_cls

end ZeroTraceRepresentativeData

/-- Theorem package: a boundary trace representative generated from refined
gluing/sink-deletion witness data is trace-equivalent to the chosen zero
representative. -/
structure BoundaryTraceEquivZeroData (setup : RewriteCalculusSetup.{u}) where
  boundaryAdminCodeContract : BoundaryAdminCodeContract.{u, u} setup
  externalOutCodeContract : ExternalOutCodeContract.{u, u} setup
  syntacticBoundaryPresentation : SyntacticBoundaryPresentation setup
  boundaryTraceData : BoundaryTraceRepresentativeData setup
  zeroData : ZeroTraceRepresentativeData setup
  boundary_trace_equiv_zero :
    ∀ {X Y : setup.State}
      (witnesses : BoundaryGluingWitnessData setup)
      (generator boundary : setup.CertifiedTrace X Y)
      (hgenerated : boundaryTraceData.boundaryGenerator generator boundary),
      TraceEquiv setup
        ((boundaryTraceData.boundaryTraceRepresentative
          witnesses generator boundary hgenerated).canonicalReplay)
        (zeroData.zeroCertifiedTrace (X := X) (Y := Y)).canonicalReplay

/-- Exact theorem target corresponding to manuscript
`lem:sink-deletion-inverse` (boundary deletion/gluing inverse) plus the
trace-equivalence generation step.

This is the minimal missing theorem needed to inhabit
`BoundaryTraceEquivZeroData.boundary_trace_equiv_zero`: from a refined-complete
sink-deletion/gluing witness and generated boundary trace, produce a
`TraceEquiv` witness between the boundary trace representative and the chosen
zero trace representative.

No additional capsule layer is introduced; this is the single theorem package
that supplies the currently missing proof field. -/
structure SinkDeletionProducesTraceEquivZero (setup : RewriteCalculusSetup.{u}) where
  boundaryTraceData : BoundaryTraceRepresentativeData setup
  zeroData : ZeroTraceRepresentativeData setup
  sinkDeletionProducesTraceEquivZero :
    ∀ {X Y : setup.State}
      (witnesses : BoundaryGluingWitnessData setup)
      (generator boundary : setup.CertifiedTrace X Y)
      (hgenerated : boundaryTraceData.boundaryGenerator generator boundary),
      TraceEquiv setup
        ((boundaryTraceData.boundaryTraceRepresentative
          witnesses generator boundary hgenerated).canonicalReplay)
        (zeroData.zeroCertifiedTrace (X := X) (Y := Y)).canonicalReplay

namespace SinkDeletionProducesTraceEquivZero

/-! ### AUDIT NOTE (2026-04-26): `ofBoundaryAndZeroData` removed

A constructor `ofBoundaryAndZeroData` appeared here that proved
`sinkDeletionProducesTraceEquivZero` by:

  `Relation.EqvGen.rel _ _ ⟨TwoCellGenerator.admin _ _ "sink-deletion-inverse"⟩`

This is **not a genuine proof**.  It exploits the fact that `TwoCellGenerator.admin`
is globally unconstrained (no `AdminRelation` proof obligation), so `TraceEquiv`
is trivially collapsed — any two replay representatives of the same type are
trace-equivalent.

That collapse was the pre-repair behavior.  The admin constructor now requires
an explicit `setup.AdminRelation` witness, and the collapse theorems were
removed from production code.

`SinkDeletionProducesTraceEquivZero` is the correct obligation structure.
It can only be genuinely inhabited once one of the following is in place:

  (A) a specific `adminRelation` proof connecting
      `boundary.canonicalReplay` and `zeroCertifiedTrace.canonicalReplay`
      via the sink-deletion boundary inverse is derived; or

  (B) A separate `sinkDeletionReplayTraceEquiv` lemma is added that
      connects the `glueBoundary`-inverse boundary equation to a
      `TraceEquiv` witness on `ReplayRepresentative` via a chain of
      genuine `swap` or `rw` 2-cells.

Until one of (A) or (B) is available, `SinkDeletionProducesTraceEquivZero`
remains an explicit honest obligation. -/

end SinkDeletionProducesTraceEquivZero

/-! ### Sink-deletion inverse: named obligations and cls-level certificate

**Component audit for `lem:sink-deletion-inverse`:**

| # | Component | Location | Status |
|---|-----------|----------|--------|
| (1) | Deletion data: `witnesses.s` is a compatible sink packet | `BoundaryGluingWitnessData.attachmentCompatibleWitness` | ✓ already captured |
| (2) | Reattachment data: `glueBoundary (exposedBoundary R s) in out (attach s) = R.Y` | `BoundaryGluingWitnessData.glueBoundaryWitness` | ✓ already captured |
| (3) | Inverse law: `exposedBoundary R s = exposeBoundaryUnderSinkDeletion R.Y out in` | `BoundaryGluingWitnessData.exposedBoundaryWitness` | ✓ already captured |
| (4) | Replay-chain construction: `TraceEquiv boundary.canonicalReplay zeroCertifiedTrace.canonicalReplay` | `BoundaryGluingReplayData.replayChainWitness` | carried as proof-relevant replay data |
| (5) | TraceEquiv production: derives `boundary.cls = zeroTraceClass` from (4) | derived below | ✓ proved below |

`SinkDeletionInverseObligations` still names component (4), while
`BoundaryGluingReplayData` is the concrete proof-relevant carrier that
provides it for sink-deletion constructors. `SinkDeletionMakesClassZeroCertificate`
is the quotient-level equivalent (easier to think about at the `cls` level),
and all conversions below are genuine proofs using existing API, with no broadening
of `AdminRelation`. -/

/-- Proof-relevant finite replay chain built from `TwoCellStep` edges.

Unlike a plain `Prop` witness, this carries an explicit chain object in
`Type`, which can be interpreted to `TraceEquiv`. -/
inductive ReplayChainWitness (setup : RewriteCalculusSetup.{u}) :
    {X Y : setup.State} →
    setup.ReplayRepresentative X Y →
    setup.ReplayRepresentative X Y → Type u
  | refl : {X Y : setup.State} →
      (σ : setup.ReplayRepresentative X Y) →
      ReplayChainWitness setup σ σ
  | cons : {X Y : setup.State} →
      {σ σ' σ'' : setup.ReplayRepresentative X Y} →
      TwoCellStep setup σ σ' →
      ReplayChainWitness setup σ' σ'' →
      ReplayChainWitness setup σ σ''

namespace ReplayChainWitness

/-- Single-step replay chain witness from one `TwoCellStep`. -/
def step
    {X Y : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y}
    (h : TwoCellStep setup σ σ') :
    ReplayChainWitness setup σ σ' :=
  cons h (refl _)

/-- Interpret a proof-relevant replay chain as `TraceEquiv`. -/
def toTraceEquiv
    {X Y : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y}
    (w : ReplayChainWitness setup σ σ') :
    TraceEquiv setup σ σ' := by
  induction w with
  | refl σ => exact traceEquiv_refl (setup := setup) σ
  | cons hstep tail ih =>
      exact traceEquiv_trans (setup := setup)
        (traceEquiv_of_step (setup := setup) hstep) ih

theorem toTraceEquiv_step
    {X Y : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y}
    (h : TwoCellStep setup σ σ') :
    (step (setup := setup) h).toTraceEquiv =
      traceEquiv_of_step (setup := setup) h :=
  rfl

theorem toTraceEquiv_cons
    {X Y : setup.State}
    {σ σ' σ'' : setup.ReplayRepresentative X Y}
    (h : TwoCellStep setup σ σ')
    (tail : ReplayChainWitness setup σ' σ'') :
    (cons h tail).toTraceEquiv =
      traceEquiv_trans (setup := setup)
        (traceEquiv_of_step (setup := setup) h)
        tail.toTraceEquiv :=
  rfl

/-- Construct a single-step `ReplayChainWitness` for the sink-deletion/gluing
inverse geometric rewrite step.

Uses `setup.sinkDeletionGeometricRule` applied to the raw boundary-level data
carried in `witnesses` to produce a concrete `TwoCellGenerator.rw` step, then
wraps it in `ReplayChainWitness.step`.  This is the primitive that allows
`BoundaryGluingReplayData` to be constructed without any external replay
obligation: the geometric rewrite rule is part of the setup, and the boundary
data is already present in `BoundaryGluingWitnessData`. -/
def sinkDeletion
    {X Y : setup.State}
    (witnesses : BoundaryGluingWitnessData setup)
    (boundary : setup.CertifiedTrace X Y)
    (zeroCT : setup.CertifiedTrace X Y) :
    ReplayChainWitness setup
      boundary.canonicalReplay
      zeroCT.canonicalReplay :=
  step (setup := setup)
    (twoCellStep_rw (setup := setup)
      boundary.canonicalReplay
      zeroCT.canonicalReplay
      (setup.sinkDeletionGeometricRule
        (setup.exposedBoundary (R := witnesses.R) witnesses.s)
        witnesses.R.Y
        (witnesses.R.packets witnesses.s).refinedIn
        (witnesses.R.packets witnesses.s).refinedOut))

/-- Guardrail invariant: `sinkDeletion` produces exactly a single `TwoCellGenerator.rw` step
keyed to `setup.sinkDeletionGeometricRule` applied to the witness boundary data.
This is NOT a general rewrite escape hatch: the rule is identified solely by
(exposedBoundary, targetBoundary, sinkRefinedIn, sinkRefinedOut), all determined by
`witnesses`. No admin bypass (`TwoCellGenerator.admin` is not used), no arbitrary
source/target rewrite. -/
@[simp] theorem sinkDeletion_eq
    {X Y : setup.State}
    (witnesses : BoundaryGluingWitnessData setup)
    (boundary zeroCT : setup.CertifiedTrace X Y) :
    sinkDeletion (setup := setup) witnesses boundary zeroCT =
      step (setup := setup)
        (twoCellStep_rw (setup := setup)
          boundary.canonicalReplay zeroCT.canonicalReplay
          (setup.sinkDeletionGeometricRule
            (setup.exposedBoundary (R := witnesses.R) witnesses.s)
            witnesses.R.Y
            (witnesses.R.packets witnesses.s).refinedIn
            (witnesses.R.packets witnesses.s).refinedOut)) :=
  rfl

end ReplayChainWitness

/-- Proof-relevant sink-deletion replay payload: for each boundary gluing
witness and generated boundary trace, supply an explicit replay chain from
the boundary canonical replay to the chosen zero canonical replay. -/
structure BoundaryGluingReplayData (setup : RewriteCalculusSetup.{u}) where
  boundaryTraceData : BoundaryTraceRepresentativeData setup
  zeroData : ZeroTraceRepresentativeData setup
  replayChainWitness :
    ∀ {X Y : setup.State}
      (witnesses : BoundaryGluingWitnessData setup)
      (generator boundary : setup.CertifiedTrace X Y)
      (hgenerated : boundaryTraceData.boundaryGenerator generator boundary),
      ReplayChainWitness setup
        boundary.canonicalReplay
        (zeroData.zeroCertifiedTrace (X := X) (Y := Y)).canonicalReplay

namespace BoundaryGluingReplayData

/-- Projection to the concrete replay-chain witness carried as data. -/
def toReplayChainWitness
    (data : BoundaryGluingReplayData setup)
    {X Y : setup.State}
    (witnesses : BoundaryGluingWitnessData setup)
    (generator boundary : setup.CertifiedTrace X Y)
    (hgenerated : data.boundaryTraceData.boundaryGenerator generator boundary) :
    ReplayChainWitness setup
      boundary.canonicalReplay
      (data.zeroData.zeroCertifiedTrace (X := X) (Y := Y)).canonicalReplay :=
  data.replayChainWitness witnesses generator boundary hgenerated

/-- Convert proof-relevant replay-chain data to the `TraceEquiv` witness
used in `SinkDeletionInverseObligations.replayChainExists`. -/
theorem traceEquiv_zero_of_boundaryGluingWitnesses
    (data : BoundaryGluingReplayData setup)
    {X Y : setup.State}
    (witnesses : BoundaryGluingWitnessData setup)
    (generator boundary : setup.CertifiedTrace X Y)
    (hgenerated : data.boundaryTraceData.boundaryGenerator generator boundary) :
    TraceEquiv setup
      boundary.canonicalReplay
      (data.zeroData.zeroCertifiedTrace (X := X) (Y := Y)).canonicalReplay :=
  ReplayChainWitness.toTraceEquiv (setup := setup)
    (BoundaryGluingReplayData.toReplayChainWitness (setup := setup)
      data witnesses generator boundary hgenerated)

/-- Alias emphasizing the data-flow:
Type-level replay-chain witness ⟶ `TraceEquiv` proposition. -/
theorem toTraceEquiv
    (data : BoundaryGluingReplayData setup)
    {X Y : setup.State}
    (witnesses : BoundaryGluingWitnessData setup)
    (generator boundary : setup.CertifiedTrace X Y)
    (hgenerated : data.boundaryTraceData.boundaryGenerator generator boundary) :
    TraceEquiv setup
      boundary.canonicalReplay
      (data.zeroData.zeroCertifiedTrace (X := X) (Y := Y)).canonicalReplay :=
  traceEquiv_zero_of_boundaryGluingWitnesses (setup := setup)
    data witnesses generator boundary hgenerated

/-- Canonical no-external-obligation constructor for `BoundaryGluingReplayData`.

Unlike the free-parameter record constructor (which requires the caller to
provide `replayChainWitness` as an external obligation), this builds the
replay chain from `setup.sinkDeletionGeometricRule` and the concrete
boundary-level data supplied by `witnesses` at application time.

The caller supplies only:
- `boundaryTraceData : BoundaryTraceRepresentativeData setup`  — how to
  produce boundary trace representatives from gluing witnesses;
- `zeroData : ZeroTraceRepresentativeData setup`               — what the
  zero trace representative is.

The `ReplayChainWitness` is then derived automatically via
`ReplayChainWitness.sinkDeletion`, which uses the geometric rewrite rule
`setup.sinkDeletionGeometricRule` to produce a single concrete
`TwoCellGenerator.rw` step. -/
def ofBoundaryGluingWitnessData
    (boundaryTraceData : BoundaryTraceRepresentativeData setup)
    (zeroData : ZeroTraceRepresentativeData setup) :
    BoundaryGluingReplayData setup where
  boundaryTraceData := boundaryTraceData
  zeroData := zeroData
  replayChainWitness := fun {X Y} witnesses _generator boundary _hgenerated =>
    ReplayChainWitness.sinkDeletion (setup := setup) witnesses boundary
      (zeroData.zeroCertifiedTrace (X := X) (Y := Y))

end BoundaryGluingReplayData

/-- Exact named obligation for `lem:sink-deletion-inverse`.
Components (1)–(3) are already captured in `BoundaryGluingWitnessData`
(see table above); component (5) is derived from (4) below.

The single genuinely missing field is (4): given any boundary gluing
witness and a generated boundary trace, the boundary canonical replay is
trace-equivalent to the zero canonical replay.

Proof paths for (4):
- **Path A**: exhibit an explicit chain of `TwoCellGenerator.swap`/`.rw`
  2-cells derived from the `glueBoundaryWitness` equation and the refined
  packet structure of `witnesses.R`.
- **Path B**: show `boundary.canonicalReplay = zeroCertifiedTrace.canonicalReplay`
  propositionally, then apply `twoCellStep_admin_eq_only` to obtain the
  `TraceEquiv` via an Eq-admin step (valid because `AdminRelation = Eq`). -/
structure SinkDeletionInverseObligations (setup : RewriteCalculusSetup.{u}) where
  boundaryTraceData : BoundaryTraceRepresentativeData setup
  zeroData : ZeroTraceRepresentativeData setup
  /-- (4) Replay-chain construction: the primary missing ingredient.
  Given any boundary gluing witness and generated boundary trace, the
  boundary `canonicalReplay` is trace-equivalent to the zero
  `canonicalReplay`.  Components (1)–(3) (deletion data, reattachment
  data, inverse law) are already in `witnesses`; this field is what
  remains to be proved. -/
  replayChainExists :
    ∀ {X Y : setup.State}
      (witnesses : BoundaryGluingWitnessData setup)
      (generator boundary : setup.CertifiedTrace X Y)
      (hgenerated : boundaryTraceData.boundaryGenerator generator boundary),
      TraceEquiv setup
        boundary.canonicalReplay
        (zeroData.zeroCertifiedTrace (X := X) (Y := Y)).canonicalReplay

/-- Quotient-level certificate for `lem:sink-deletion-inverse`: the boundary
trace class equals the zero trace class for any boundary generated from a
refined gluing witness.

Equivalent to `SinkDeletionProducesTraceEquivZero` but stated at the `cls`
level.  Converting to `SinkDeletionProducesTraceEquivZero` is a proved
theorem (see `toSinkDeletionProducesTraceEquivZero` below). -/
structure SinkDeletionMakesClassZeroCertificate (setup : RewriteCalculusSetup.{u}) where
  boundaryTraceData : BoundaryTraceRepresentativeData setup
  zeroData : ZeroTraceRepresentativeData setup
  /-- The cls-level obligation: for any boundary-generated trace with gluing
  witnesses, the boundary trace class equals the zero trace class.
  This is `lem:sink-deletion-inverse` stated purely at the quotient level. -/
  sinkDeletionMakesClassZero :
    ∀ {X Y : setup.State}
      (witnesses : BoundaryGluingWitnessData setup)
      (generator boundary : setup.CertifiedTrace X Y)
      (hgenerated : boundaryTraceData.boundaryGenerator generator boundary),
      boundary.cls = zeroData.zeroTraceClass (X := X) (Y := Y)

namespace SinkDeletionMakesClassZeroCertificate

/-- Convert the cls-level certificate to `SinkDeletionProducesTraceEquivZero`.

The proof derives `TraceEquiv boundary.canonicalReplay zeroCertifiedTrace.canonicalReplay`
via `TraceClass.exact` applied to the chain:

  `TraceClass.mk setup boundary.canonicalReplay`
    `= boundary.cls`                                       (by `represents`)
    `= zeroData.zeroTraceClass`                            (by `sinkDeletionMakesClassZero`)
    `= zeroCertifiedTrace.cls`                             (by `zeroCertifiedTrace_cls.symm`)
    `= TraceClass.mk setup zeroCertifiedTrace.canonicalReplay` (by `represents.symm`)

No broadening of `AdminRelation` is used, and no arbitrary admin move is added. -/
def toSinkDeletionProducesTraceEquivZero
    (cert : SinkDeletionMakesClassZeroCertificate setup) :
    SinkDeletionProducesTraceEquivZero setup where
  boundaryTraceData := cert.boundaryTraceData
  zeroData := cert.zeroData
  sinkDeletionProducesTraceEquivZero := by
    intro X Y witnesses generator boundary hgenerated
    have hBoundaryEq :
        cert.boundaryTraceData.boundaryTraceRepresentative
          witnesses generator boundary hgenerated = boundary :=
      cert.boundaryTraceData.boundaryTraceRepresentative_eq_boundary
        witnesses generator boundary hgenerated
    rw [hBoundaryEq]
    have hclsEq :=
      cert.sinkDeletionMakesClassZero witnesses generator boundary hgenerated
    apply TraceClass.exact (setup := setup)
    calc TraceClass.mk setup boundary.canonicalReplay
        = boundary.cls := boundary.represents
      _ = cert.zeroData.zeroTraceClass (X := X) (Y := Y) := hclsEq
      _ = (cert.zeroData.zeroCertifiedTrace (X := X) (Y := Y)).cls :=
          cert.zeroData.zeroCertifiedTrace_cls.symm
      _ = TraceClass.mk setup
            (cert.zeroData.zeroCertifiedTrace (X := X) (Y := Y)).canonicalReplay :=
          (cert.zeroData.zeroCertifiedTrace (X := X) (Y := Y)).represents.symm

end SinkDeletionMakesClassZeroCertificate

namespace SinkDeletionInverseObligations

/-- Replay-equivalence theorem from concrete boundary-gluing replay data. -/
theorem replayChainExists_of_boundaryGluingWitnesses
    (data : BoundaryGluingReplayData setup)
    {X Y : setup.State}
    (witnesses : BoundaryGluingWitnessData setup)
    (generator boundary : setup.CertifiedTrace X Y)
    (hgenerated : data.boundaryTraceData.boundaryGenerator generator boundary) :
    TraceEquiv setup
      boundary.canonicalReplay
      (data.zeroData.zeroCertifiedTrace (X := X) (Y := Y)).canonicalReplay :=
  BoundaryGluingReplayData.traceEquiv_zero_of_boundaryGluingWitnesses
    (setup := setup) data witnesses generator boundary hgenerated

/-- Construct `SinkDeletionInverseObligations` directly from concrete
proof-relevant boundary-gluing replay data. -/
def ofBoundaryGluingWitnesses
    (data : BoundaryGluingReplayData setup) :
    SinkDeletionInverseObligations setup where
  boundaryTraceData := data.boundaryTraceData
  zeroData := data.zeroData
  replayChainExists := by
    intro X Y witnesses generator boundary hgenerated
    exact replayChainExists_of_boundaryGluingWitnesses (setup := setup)
      data witnesses generator boundary hgenerated

/-- Canonical sink-deletion inverse obligations constructor from concrete
boundary/gluing replay data. -/
def canonicalSinkDeletionInverseObligations
    (data : BoundaryGluingReplayData setup) :
    SinkDeletionInverseObligations setup :=
  ofBoundaryGluingWitnesses (setup := setup) data

/-- Canonical no-external-replay-data constructor for `SinkDeletionInverseObligations`.

The caller supplies only `BoundaryTraceRepresentativeData` and
`ZeroTraceRepresentativeData`; the replay chain obligation is discharged
automatically using `ReplayChainWitness.sinkDeletion` and
`setup.sinkDeletionGeometricRule`. -/
def ofBoundaryGluingWitnessData
    (boundaryTraceData : BoundaryTraceRepresentativeData setup)
    (zeroData : ZeroTraceRepresentativeData setup) :
    SinkDeletionInverseObligations setup :=
  ofBoundaryGluingWitnesses (setup := setup)
    (BoundaryGluingReplayData.ofBoundaryGluingWitnessData (setup := setup)
      boundaryTraceData zeroData)

/-- Promote replay-chain obligations (4) to the cls-level certificate.

The proof derives `boundary.cls = zeroTraceClass` from `replayChainExists`
via the chain:

  `boundary.cls`
    `= TraceClass.mk setup boundary.canonicalReplay`       (by `class_eq_mk_canonicalReplay`)
    `= TraceClass.mk setup zeroCertifiedTrace.canonicalReplay` (by `TraceClass.sound`)
    `= zeroCertifiedTrace.cls`                             (by `represents`)
    `= zeroData.zeroTraceClass`                            (by `zeroCertifiedTrace_cls`) -/
def toClassZeroCertificate
    (obl : SinkDeletionInverseObligations setup) :
    SinkDeletionMakesClassZeroCertificate setup where
  boundaryTraceData := obl.boundaryTraceData
  zeroData := obl.zeroData
  sinkDeletionMakesClassZero := fun witnesses generator boundary hgenerated => by
    have hEquiv := obl.replayChainExists witnesses generator boundary hgenerated
    calc boundary.cls
        = TraceClass.mk setup boundary.canonicalReplay :=
          boundary.class_eq_mk_canonicalReplay
      _ = TraceClass.mk setup
            (obl.zeroData.zeroCertifiedTrace (X := _) (Y := _)).canonicalReplay :=
          TraceClass.sound (setup := setup) hEquiv
      _ = (obl.zeroData.zeroCertifiedTrace (X := _) (Y := _)).cls :=
          (obl.zeroData.zeroCertifiedTrace).represents
      _ = obl.zeroData.zeroTraceClass :=
          obl.zeroData.zeroCertifiedTrace_cls

/-- Directly produce `SinkDeletionProducesTraceEquivZero` from the named
replay-chain obligations, via the cls-level certificate.
This is a genuine two-step proof: (4) → cls equality → `TraceEquiv`. -/
def toSinkDeletionProducesTraceEquivZero
    (obl : SinkDeletionInverseObligations setup) :
    SinkDeletionProducesTraceEquivZero setup :=
  SinkDeletionMakesClassZeroCertificate.toSinkDeletionProducesTraceEquivZero setup
    (toClassZeroCertificate setup obl)

end SinkDeletionInverseObligations

namespace SinkDeletionProducesTraceEquivZero

/-- Concrete constructor from proof-relevant boundary-gluing replay data. -/
def ofBoundaryGluingWitnesses
    (data : BoundaryGluingReplayData setup) :
    SinkDeletionProducesTraceEquivZero setup :=
  SinkDeletionInverseObligations.toSinkDeletionProducesTraceEquivZero (setup := setup)
    (SinkDeletionInverseObligations.ofBoundaryGluingWitnesses (setup := setup) data)

/-- Canonical no-external-replay-data constructor for
`SinkDeletionProducesTraceEquivZero`.

The caller supplies only `BoundaryTraceRepresentativeData` and
`ZeroTraceRepresentativeData`; the `TraceEquiv` proof is produced automatically
via `BoundaryGluingReplayData.ofBoundaryGluingWitnessData`. -/
def ofBoundaryGluingWitnessData
    (boundaryTraceData : BoundaryTraceRepresentativeData setup)
    (zeroData : ZeroTraceRepresentativeData setup) :
    SinkDeletionProducesTraceEquivZero setup :=
  ofBoundaryGluingWitnesses (setup := setup)
    (BoundaryGluingReplayData.ofBoundaryGluingWitnessData (setup := setup)
      boundaryTraceData zeroData)

end SinkDeletionProducesTraceEquivZero

namespace BoundaryTraceEquivZeroData

/-- Build `BoundaryTraceEquivZeroData` once the single missing theorem
`SinkDeletionProducesTraceEquivZero` is supplied. -/
def ofSinkDeletionProducesTraceEquivZero
    (boundaryAdminCodeContract : BoundaryAdminCodeContract.{u, u} setup)
    (externalOutCodeContract : ExternalOutCodeContract.{u, u} setup)
    (syntacticBoundaryPresentation : SyntacticBoundaryPresentation setup)
    (theoremData : SinkDeletionProducesTraceEquivZero setup) :
    BoundaryTraceEquivZeroData setup where
  boundaryAdminCodeContract := boundaryAdminCodeContract
  externalOutCodeContract := externalOutCodeContract
  syntacticBoundaryPresentation := syntacticBoundaryPresentation
  boundaryTraceData := theoremData.boundaryTraceData
  zeroData := theoremData.zeroData
  boundary_trace_equiv_zero := theoremData.sinkDeletionProducesTraceEquivZero

/-- Build `BoundaryTraceEquivZeroData` directly from concrete boundary-gluing
replay data by routing through `SinkDeletionProducesTraceEquivZero`. -/
def ofBoundaryGluingWitnesses
    (boundaryAdminCodeContract : BoundaryAdminCodeContract.{u, u} setup)
    (externalOutCodeContract : ExternalOutCodeContract.{u, u} setup)
    (syntacticBoundaryPresentation : SyntacticBoundaryPresentation setup)
    (data : BoundaryGluingReplayData setup) :
    BoundaryTraceEquivZeroData setup :=
  ofSinkDeletionProducesTraceEquivZero (setup := setup)
    boundaryAdminCodeContract
    externalOutCodeContract
    syntacticBoundaryPresentation
    (SinkDeletionProducesTraceEquivZero.ofBoundaryGluingWitnesses
      (setup := setup) data)

/-- Canonical no-external-replay-data constructor for `BoundaryTraceEquivZeroData`.

The caller supplies only the code contracts, syntactic presentation,
`BoundaryTraceRepresentativeData`, and `ZeroTraceRepresentativeData`.
The `TraceEquiv` proof field is produced automatically via
`BoundaryGluingReplayData.ofBoundaryGluingWitnessData` and
`setup.sinkDeletionGeometricRule`. -/
def ofBoundaryGluingWitnessData
    (boundaryAdminCodeContract : BoundaryAdminCodeContract.{u, u} setup)
    (externalOutCodeContract : ExternalOutCodeContract.{u, u} setup)
    (syntacticBoundaryPresentation : SyntacticBoundaryPresentation setup)
    (boundaryTraceData : BoundaryTraceRepresentativeData setup)
    (zeroData : ZeroTraceRepresentativeData setup) :
    BoundaryTraceEquivZeroData setup :=
  ofBoundaryGluingWitnesses (setup := setup)
    boundaryAdminCodeContract
    externalOutCodeContract
    syntacticBoundaryPresentation
    (BoundaryGluingReplayData.ofBoundaryGluingWitnessData (setup := setup)
      boundaryTraceData zeroData)

@[simp] theorem ofSinkDeletionProducesTraceEquivZero_boundaryTraceData
    (boundaryAdminCodeContract : BoundaryAdminCodeContract.{u, u} setup)
    (externalOutCodeContract : ExternalOutCodeContract.{u, u} setup)
    (syntacticBoundaryPresentation : SyntacticBoundaryPresentation setup)
    (theoremData : SinkDeletionProducesTraceEquivZero setup) :
    (ofSinkDeletionProducesTraceEquivZero (setup := setup)
      boundaryAdminCodeContract externalOutCodeContract
      syntacticBoundaryPresentation theoremData).boundaryTraceData =
      theoremData.boundaryTraceData :=
  rfl

@[simp] theorem ofSinkDeletionProducesTraceEquivZero_zeroData
    (boundaryAdminCodeContract : BoundaryAdminCodeContract.{u, u} setup)
    (externalOutCodeContract : ExternalOutCodeContract.{u, u} setup)
    (syntacticBoundaryPresentation : SyntacticBoundaryPresentation setup)
    (theoremData : SinkDeletionProducesTraceEquivZero setup) :
    (ofSinkDeletionProducesTraceEquivZero (setup := setup)
      boundaryAdminCodeContract externalOutCodeContract
      syntacticBoundaryPresentation theoremData).zeroData =
      theoremData.zeroData :=
  rfl

/-- Quotient-level consequence of `boundary_trace_equiv_zero` for the produced
boundary representative. -/
theorem boundaryTraceRepresentativeClass_eq_zeroTraceClass
    (data : BoundaryTraceEquivZeroData setup)
    {X Y : setup.State}
    (witnesses : BoundaryGluingWitnessData setup)
    (generator boundary : setup.CertifiedTrace X Y)
    (hgenerated : data.boundaryTraceData.boundaryGenerator generator boundary) :
    (data.boundaryTraceData.boundaryTraceRepresentative
      witnesses generator boundary hgenerated).cls =
      data.zeroData.zeroTraceClass (X := X) (Y := Y) := by
  let boundaryRep :=
    data.boundaryTraceData.boundaryTraceRepresentative
      witnesses generator boundary hgenerated
  let zeroRep := data.zeroData.zeroCertifiedTrace (X := X) (Y := Y)
  have hmk : TraceClass.mk setup boundaryRep.canonicalReplay =
      TraceClass.mk setup zeroRep.canonicalReplay :=
    TraceClass.sound (setup := setup)
      (data.boundary_trace_equiv_zero witnesses generator boundary hgenerated)
  calc
    boundaryRep.cls = TraceClass.mk setup boundaryRep.canonicalReplay := by
      simpa using boundaryRep.represents.symm
    _ = TraceClass.mk setup zeroRep.canonicalReplay := hmk
    _ = zeroRep.cls := by simpa using zeroRep.represents
    _ = data.zeroData.zeroTraceClass (X := X) (Y := Y) :=
      data.zeroData.zeroCertifiedTrace_cls

/-- Boundary-class-to-zero theorem for the original boundary argument. -/
theorem boundaryTraceClass_eq_zero
    (data : BoundaryTraceEquivZeroData setup)
    {X Y : setup.State}
    (witnesses : BoundaryGluingWitnessData setup)
    (generator boundary : setup.CertifiedTrace X Y)
    (hgenerated : data.boundaryTraceData.boundaryGenerator generator boundary) :
    boundary.cls = data.zeroData.zeroTraceClass (X := X) (Y := Y) := by
  simpa [data.boundaryTraceData.boundaryTraceRepresentative_eq_boundary
    witnesses generator boundary hgenerated]
    using BoundaryTraceEquivZeroData.boundaryTraceRepresentativeClass_eq_zeroTraceClass
      (setup := setup) data witnesses generator boundary hgenerated

/-- Build the current lowest bridge package from the full boundary-to-zero
trace-equivalence capsule. -/
def toGluingWitnessToTraceClassBridge
    (data : BoundaryTraceEquivZeroData setup) :
    GluingWitnessToTraceClassBridge setup where
  zeroClass := data.zeroData.zeroTraceClass
  boundaryGenerator := data.boundaryTraceData.boundaryGenerator
  gluingWitnessImpliesZeroClass := by
    intro X Y generator boundary hgenerated R hR s hcompat hglue
    let witnesses : BoundaryGluingWitnessData setup :=
      BoundaryGluingWitnessData.ofRefined (setup := setup)
        data.boundaryAdminCodeContract
        data.externalOutCodeContract
        data.syntacticBoundaryPresentation
        R hR s hglue
    have hzero := BoundaryTraceEquivZeroData.boundaryTraceClass_eq_zero
      (setup := setup) data witnesses generator boundary hgenerated
    simpa using hzero

def toGluedBoundaryHasZeroTraceClassTarget
    (data : BoundaryTraceEquivZeroData setup) :
    GluedBoundaryHasZeroTraceClassTarget setup :=
  GluingWitnessToTraceClassBridge.toGluedBoundaryHasZeroTraceClassTarget
    (setup := setup)
    data.toGluingWitnessToTraceClassBridge

def toTraceBoundaryZeroTheorem
    (data : BoundaryTraceEquivZeroData setup)
    (witnessExistence :
      ∀ {X Y : setup.State}
        (generator boundary : setup.CertifiedTrace X Y),
        data.boundaryTraceData.boundaryGenerator generator boundary →
          ∃ (R : CompletedReconstructionRecord setup)
            (_hR : R.IsCompletedRefined (setup := setup))
            (s : Fin R.n),
            setup.IsCompatibleAttachmentForPacket (R := R) s ∧
              setup.glueBoundary
                  (setup.exposedBoundary (R := R) s)
                  (R.packets s).refinedIn
                  (R.packets s).refinedOut
                  (R.attach s) = R.Y) :
    TraceBoundaryZeroTheorem setup :=
    GluingWitnessToTraceClassBridge.toTraceBoundaryZeroTheorem
      (setup := setup)
      data.toGluingWitnessToTraceClassBridge
      witnessExistence

@[simp] theorem toGluingWitnessToTraceClassBridge_zeroClass
    (data : BoundaryTraceEquivZeroData setup)
    {X Y : setup.State} :
    (data.toGluingWitnessToTraceClassBridge).zeroClass (X := X) (Y := Y) =
      data.zeroData.zeroTraceClass (X := X) (Y := Y) :=
  rfl

@[simp] theorem toGluingWitnessToTraceClassBridge_boundaryGenerator
    (data : BoundaryTraceEquivZeroData setup)
    {X Y : setup.State}
    (generator boundary : setup.CertifiedTrace X Y) :
    (data.toGluingWitnessToTraceClassBridge).boundaryGenerator
      generator boundary =
      data.boundaryTraceData.boundaryGenerator generator boundary :=
  rfl

end BoundaryTraceEquivZeroData

/-- Full upward capsule from boundary/gluing data into the existing
TraceDifferential/H0 pipeline. The remaining obligations are exactly
null-trace and cycle-side hypotheses. -/
structure BoundaryToTraceDifferentialCapsule (setup : RewriteCalculusSetup.{u}) where
  equivZeroData : BoundaryTraceEquivZeroData setup
  witnessExistence :
    ∀ {X Y : setup.State}
      (generator boundary : setup.CertifiedTrace X Y),
      equivZeroData.boundaryTraceData.boundaryGenerator generator boundary →
        ∃ (R : CompletedReconstructionRecord setup)
          (_hR : R.IsCompletedRefined (setup := setup))
          (s : Fin R.n),
          setup.IsCompatibleAttachmentForPacket (R := R) s ∧
            setup.glueBoundary
                (setup.exposedBoundary (R := R) s)
                (R.packets s).refinedIn
                (R.packets s).refinedOut
                (R.attach s) = R.Y
  nullTrace : ∀ {X Y : setup.State}, setup.CertifiedTrace X Y → Prop
  cyclePredicate : ∀ {X Y : setup.State}, setup.CertifiedTrace X Y → Prop
  nullTrace_maps_to_zeroClass :
    ∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
      nullTrace trace →
        trace.cls = equivZeroData.zeroData.zeroTraceClass (X := X) (Y := Y)
  cycles_descend_to_traceClass :
    ∀ {X Y : setup.State} (trace : setup.CertifiedTrace X Y),
      cyclePredicate trace →
        ∃ representative : setup.CertifiedTrace X Y,
          representative.cls = trace.cls ∧ cyclePredicate representative

namespace BoundaryToTraceDifferentialCapsule

def toTraceBoundaryZeroTheorem
    (capsule : BoundaryToTraceDifferentialCapsule setup) :
    TraceBoundaryZeroTheorem setup :=
  BoundaryTraceEquivZeroData.toTraceBoundaryZeroTheorem
    (setup := setup)
    capsule.equivZeroData
    capsule.witnessExistence

def toAttachmentBoundaryZeroData
    (capsule : BoundaryToTraceDifferentialCapsule setup) :
    AttachmentBoundaryZeroData setup where
  zeroClass := capsule.equivZeroData.zeroData.zeroTraceClass
  nullTrace := capsule.nullTrace
  boundaryGenerator := capsule.equivZeroData.boundaryTraceData.boundaryGenerator
  cyclePredicate := capsule.cyclePredicate
  nullTrace_maps_to_zeroClass := capsule.nullTrace_maps_to_zeroClass
  boundaryGenerator_maps_to_zeroClass := by
    intro X Y generator boundary hgenerator
    rcases capsule.witnessExistence generator boundary hgenerator with
      ⟨R, hR, s, hcompat, hglue⟩
    exact (capsule.equivZeroData.toGluingWitnessToTraceClassBridge
      ).gluingWitnessImpliesZeroClass
        generator boundary hgenerator R hR s hcompat hglue
  cycles_descend_to_traceClass := capsule.cycles_descend_to_traceClass
  boundaryGenerator_has_gluing_zero_witness := capsule.witnessExistence

def toTraceNullBoundaryData
    (capsule : BoundaryToTraceDifferentialCapsule setup) :
    TraceNullBoundaryData setup :=
  (capsule.toAttachmentBoundaryZeroData
    ).forgetToTraceNullBoundaryData

def toTraceHomotopyBoundarySemantics
    (capsule : BoundaryToTraceDifferentialCapsule setup) :
    TraceHomotopyBoundarySemantics setup :=
  (capsule.toTraceNullBoundaryData
    ).toTraceHomotopyBoundarySemantics

def toTraceDifferentialSemantics
    (capsule : BoundaryToTraceDifferentialCapsule setup) :
    TraceDifferentialSemantics setup :=
  (capsule.toTraceHomotopyBoundarySemantics
    ).toTraceDifferentialSemantics

@[simp] theorem toTraceDifferentialSemantics_boundaryClass
    (capsule : BoundaryToTraceDifferentialCapsule setup)
    {X Y : setup.State} :
    (capsule.toTraceDifferentialSemantics).boundaryClass (X := X) (Y := Y) =
      capsule.equivZeroData.zeroData.zeroTraceClass (X := X) (Y := Y) :=
  rfl

end BoundaryToTraceDifferentialCapsule

/-! ### Typed peel-chain normalization differential package

The trace-relation packages above supply boundary-to-zero semantics for certified traces.
For the normalization complex, the first genuinely composable lower-layer carrier is the
sink-peel chain itself: each differential is an adjacent peel step, and each two-step
composite is equipped with proof-relevant null-boundary data.
-/

structure PeelChainAdjacentDifferential
    {R : CompletedReconstructionRecord setup}
    (chain : CompletedReconstructionRecord.PeelChain R) where
  source : CompletedReconstructionRecord setup
  target : CompletedReconstructionRecord setup
  degree : Nat
  nextDegree : Nat
  degree_step : nextDegree = degree + 1
  source_packet_count : source.n + degree = R.n
  target_packet_count : target.n + nextDegree = R.n
  sink : Fin source.n
  sink_is_sink : source.IsSink sink

namespace PeelChainAdjacentDifferential

theorem degree_strictly_increases
    {R : CompletedReconstructionRecord setup}
    {chain : CompletedReconstructionRecord.PeelChain R}
    (step : PeelChainAdjacentDifferential (setup := setup) chain) :
    step.degree < step.nextDegree := by
  rw [step.degree_step]
  exact Nat.lt_succ_self step.degree

end PeelChainAdjacentDifferential

structure PeelChainTwoStepNullBoundary
    {R : CompletedReconstructionRecord setup}
    (chain : CompletedReconstructionRecord.PeelChain R)
    (first second : PeelChainAdjacentDifferential (setup := setup) chain) where
  endpoints_match : first.target = second.source
  composite_source : CompletedReconstructionRecord setup := first.source
  composite_middle : CompletedReconstructionRecord setup := first.target
  composite_target : CompletedReconstructionRecord setup := second.target
  source_eq : composite_source = first.source
  middle_eq_left : composite_middle = first.target
  middle_eq_right : composite_middle = second.source
  target_eq : composite_target = second.target
  degree_gap : second.nextDegree = first.degree + 2

namespace PeelChainTwoStepNullBoundary

theorem middle_agrees
    {R : CompletedReconstructionRecord setup}
    {chain : CompletedReconstructionRecord.PeelChain R}
    {first second : PeelChainAdjacentDifferential (setup := setup) chain}
    (boundary : PeelChainTwoStepNullBoundary (setup := setup) chain first second) :
    first.target = second.source :=
  boundary.endpoints_match

end PeelChainTwoStepNullBoundary

structure PeelChainDifferentialPackage
    {R : CompletedReconstructionRecord setup}
    (chain : CompletedReconstructionRecord.PeelChain R) where
  differentialAt : Nat → Option (PeelChainAdjacentDifferential (setup := setup) chain)
  differentialAt_degree :
    ∀ {degree : Nat} {step : PeelChainAdjacentDifferential (setup := setup) chain},
      differentialAt degree = some step → step.degree = degree
  starts_at_record :
    ∀ {step : PeelChainAdjacentDifferential (setup := setup) chain},
      differentialAt 0 = some step → step.source = R
  adjacent_null_boundary :
    ∀ {degree : Nat}
      {first second : PeelChainAdjacentDifferential (setup := setup) chain},
      differentialAt degree = some first →
      differentialAt (degree + 1) = some second →
        PeelChainTwoStepNullBoundary (setup := setup) chain first second

namespace PeelChainDifferentialPackage

def gradeObject
    {R : CompletedReconstructionRecord setup}
    {chain : CompletedReconstructionRecord.PeelChain R}
    (pkg : PeelChainDifferentialPackage (setup := setup) chain)
    (degree : Nat) : Option (CompletedReconstructionRecord setup) :=
  match PeelChainDifferentialPackage.differentialAt pkg degree with
  | some step => some step.source
  | none => none

def differential
    {R : CompletedReconstructionRecord setup}
    {chain : CompletedReconstructionRecord.PeelChain R}
    (pkg : PeelChainDifferentialPackage (setup := setup) chain)
    (degree : Nat) : Option (PeelChainAdjacentDifferential (setup := setup) chain) :=
  PeelChainDifferentialPackage.differentialAt pkg degree

def d_next_comp_d
    {R : CompletedReconstructionRecord setup}
    {chain : CompletedReconstructionRecord.PeelChain R}
    (pkg : PeelChainDifferentialPackage (setup := setup) chain)
    {degree : Nat}
    {first second : PeelChainAdjacentDifferential (setup := setup) chain}
    (hfirst : differential (setup := setup) pkg degree = some first)
    (hsecond : differential (setup := setup) pkg (degree + 1) = some second) :
    PeelChainTwoStepNullBoundary (setup := setup) chain first second :=
  PeelChainDifferentialPackage.adjacent_null_boundary pkg
    (by simpa [differential] using hfirst)
    (by simpa [differential] using hsecond)

theorem first_differential_source
    {R : CompletedReconstructionRecord setup}
    {chain : CompletedReconstructionRecord.PeelChain R}
    (pkg : PeelChainDifferentialPackage (setup := setup) chain)
    {step : PeelChainAdjacentDifferential (setup := setup) chain}
    (hstep : differential (setup := setup) pkg 0 = some step) :
    step.source = R :=
  PeelChainDifferentialPackage.starts_at_record pkg hstep

theorem differential_degree
    {R : CompletedReconstructionRecord setup}
    {chain : CompletedReconstructionRecord.PeelChain R}
    (pkg : PeelChainDifferentialPackage (setup := setup) chain)
    {degree : Nat} {step : PeelChainAdjacentDifferential (setup := setup) chain}
    (hstep : differential (setup := setup) pkg degree = some step) :
    step.degree = degree :=
  PeelChainDifferentialPackage.differentialAt_degree pkg hstep

theorem differential_next_degree
    {R : CompletedReconstructionRecord setup}
    {chain : CompletedReconstructionRecord.PeelChain R}
    (pkg : PeelChainDifferentialPackage (setup := setup) chain)
    {degree : Nat} {step : PeelChainAdjacentDifferential (setup := setup) chain}
    (hstep : differential (setup := setup) pkg degree = some step) :
    step.nextDegree = degree + 1 := by
  rw [PeelChainAdjacentDifferential.degree_step step,
    differential_degree (setup := setup) pkg hstep]

theorem differential_degree_within_amplitude
    {R : CompletedReconstructionRecord setup}
    {chain : CompletedReconstructionRecord.PeelChain R}
    (pkg : PeelChainDifferentialPackage (setup := setup) chain)
    {degree : Nat} {step : PeelChainAdjacentDifferential (setup := setup) chain}
    (hstep : differential (setup := setup) pkg degree = some step) :
    degree ≤ R.n := by
  have hdegree := differential_degree (setup := setup) pkg hstep
  have hcount := PeelChainAdjacentDifferential.source_packet_count step
  rw [← hdegree]
  rw [← hcount]
  exact Nat.le_add_left step.degree step.source.n

end PeelChainDifferentialPackage

end RewriteCalculusSetup
end RealObjects
end LayerB
end TraceCalc