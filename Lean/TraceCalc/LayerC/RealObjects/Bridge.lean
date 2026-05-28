import TraceCalc.LayerB.RealObjects.RewriteCalculus
import TraceCalc.LayerB.Foundations.Occurrence

/-!
# Bridge: Foundations → RewriteCalculusSetup

**Real-objects path, Lane B cycle 5 (2026-04-23).**

This file builds the **bridge** that instantiates the opaque
`RewriteCalculusSetup` of `TraceCalc.LayerB.RealObjects.RewriteCalculus`
(Lane A, cycle 1) using the real foundational syntax of Lane B
cycles 1–4: `Sort_`, `Expr`, `Pat`, `BoundaryCirquent`, `Goal`,
`State`, `Doctrine`, `Occurrence`, `replace`,
`PrimitiveCertifiedDeclaration`.

## Why this is the gating cycle of Phase 2

Per the project plan ([/memories/session/plan.md](/memories/session/plan.md)
Phase 2C), the *cycle-5 bridge* is the discharge of obligation §2C —
*"every opaque carrier in `RewriteCalculusSetup` has at least one
concrete instance built from Lane B Foundations"*. Before this file,
Lane A theorems on `RewriteCalculusSetup` were valid against any
inhabitant; after this file, they are valid against the concrete
inhabitant produced from any `Doctrine D` plus the small set of
*non-foundational* carrier data (support payloads, replay
certificates, gluing witnesses, boundary objects, geometric rewrite
rules) that the manuscript does not derive from syntax.

## Universe accounting

The foundational `State Sig` lives in `Type (u+1)` (because
`DefinitionEnvironment.localDeclarations : Type u` is itself a
type-valued field). The Lane A `RewriteCalculusSetup` is a
single-universe structure with `State : Type u`. To make the bridge
honest at the universe level we instantiate `RewriteCalculusSetup`
at universe `u+1` and use `ULift.{u+1, u}` to embed the small
foundational types (`D.P0`, `Sort_ D`, `ExprCirquent`, `Goal`,
`Sig.Op`, `R_index`, `Occurrence`) into `Type (u+1)`. No information
is destroyed; the witness theorems below recover the foundations'
types from the bridge's fields via `ULift.down`.

## Honest scope

* **Syntactic fields** are mapped to the cycle-1/2/4 inductives
  directly (lifted via `ULift` where the universe accounting requires
  it).
* **Doctrine-derived field** `admissible` is mapped via
  `Decidable.decide` on `Dc.admissible`.
* **Non-syntactic fields** are taken as inputs in the
  `BridgeAuxiliaryData` bundle. The manuscript itself defers their
  content to `def:carrier` (L429), `def:primitive-support-payload`
  (L679), the certificate prose (L617), `def:replay-representative`
  (L731), the boundary-exposure recipe (L1224), `Glue` (L1180), and
  `R_geom` (defined elsewhere).
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

open TraceCalc.LayerB.Foundations

/-! ### Auxiliary (non-foundational) data required by the bridge

All carrier types live in `Type (u+1)` to match the bridge's
universe. -/

/-- Non-foundational carrier data needed to instantiate
`RewriteCalculusSetup` from a `Doctrine`. -/
structure BridgeAuxiliaryData {D : PrimitiveInterfaceData.{u}}
    (Dc : Doctrine D) where
  /-- The carrier `𝒫 = {(p_k, I_k)}` of `def:carrier`
  (`our_paper_draft.tex` L429). -/
  Carrier : Type (u+1)
  /-- The carrier under consideration. -/
  carrier : Carrier
  /-- The pattern-admission gate of `def:carrier` (L433). -/
  sanctionedByPatternAdmissionGate :
    Carrier → (i : Dc.R_index) → (G : Foundations.Goal Dc.sig) →
      Foundations.Occurrence Dc (Dc.R i) G → Bool
  /-- Support data of `def:primitive-certified-declaration` clause (3)
  (L617). -/
  SupportData : Dc.R_index → Foundations.Goal Dc.sig → Type (u+1)
  /-- Named consumed semantic resources `Res_in(P)`
  (`def:primitive-support-payload`, L679). -/
  consumes :
    {i : Dc.R_index} → {G : Foundations.Goal Dc.sig} →
      SupportData i G → Type (u+1)
  /-- Named exported semantic resources `Res_out(P)`. -/
  exports :
    {i : Dc.R_index} → {G : Foundations.Goal Dc.sig} →
      SupportData i G → Type (u+1)
  /-- Replay certificate of `def:primitive-certified-declaration`
  clause (4) (L618). -/
  ReplayCertificate : Dc.R_index → Foundations.State Dc.sig → Type (u+1)
  /-- Boundary objects `X, Y` along which a replay representative
  runs (`def:replay-representative`, L731). -/
  BoundaryObject : Type (u+1)
  /-- The boundary object of a state. -/
  boundaryOf : Foundations.State Dc.sig → BoundaryObject
  /-- Refined interface labels `In^♯`/`Out^♯`
  (`rem:refined-interfaces-derived`, L671 + L679 + L686). -/
  RefinedInterface : Type (u+1)
  /-- Reattachment / gluing witness data
  (`thm:canonical-reconstruction-algorithm`, Step 3, L1180). -/
  GluingWitness : Type (u+1)
  /-- Boolean compatibility check for an attachment witness
  (C2 of `def:completed-reconstruction-record`, L1128). -/
  attachmentCompatible :
    GluingWitness → BoundaryObject → BoundaryObject →
      List RefinedInterface → List RefinedInterface → Bool
  /-- Boundary exposure under sink deletion (`def:boundary-exposure`,
  L1224). -/
  exposeBoundaryUnderSinkDeletion :
    BoundaryObject → List RefinedInterface → List RefinedInterface →
      BoundaryObject
  /-- Boundary-level Glue
  (`thm:canonical-reconstruction-algorithm` Step 3, L1180). -/
  glueBoundary :
    BoundaryObject → List RefinedInterface → List RefinedInterface →
      GluingWitness → BoundaryObject
  /-- Geometric rewrite rules `R_geom` (`def:trace-equivalence`
  clause (c), L754). -/
  GeometricRewriteRule : Type (u+1)
  /-- The canonical geometric rewrite rule for the sink-deletion/gluing inverse
  (`lem:sink-deletion-inverse`, L1240).  Mirrors the `sinkDeletionGeometricRule`
  field of `RewriteCalculusSetup`. -/
  sinkDeletionGeometricRule :
    BoundaryObject → BoundaryObject →
    List RefinedInterface → List RefinedInterface →
    GeometricRewriteRule

/-! ### The bridge -/

/-- **The Lane B → Lane A bridge.** Given a doctrine and the
auxiliary non-foundational data, produce a `RewriteCalculusSetup`
whose syntactic fields unfold to the real cycle-1/2/4 inductives
(modulo `ULift` for universe accounting).

* `Slot := ULift D.P0` (manuscript L380).
* `Sort_ := ULift (Foundations.Sort_ D)` (`def:intrinsic-sort-system`,
  L388).
* `Cirquent := ULift (Foundations.ExprCirquent Dc.sig)`
  (`def:expression-cirquent`, L553).
* `Goal := ULift (Foundations.Goal Dc.sig)`
  (`def:boundary-cirquent-and-goal`, L557).
* `State := Foundations.State Dc.sig` (`def:state`, L565) — already
  at the bridge's target universe.
* `OperationSymbol := ULift Dc.sig.Op` (manuscript L520).
* `RewriteScheme := ULift Dc.R_index` (`def:doctrine-definition`
  clause (ii), L450).
* `admissible i S := decide (Dc.admissible i.down ⟨S.goal, PUnit⟩)`
  — delegates to the doctrine's decidable predicate (manuscript
  L452, L456); the opaque `LocalCirquentState.positional` is filled
  with `PUnit`.
* `TypedOccurrenceMap i G := ULift (Foundations.Occurrence …)` —
  exposes the cycle-4 `Occurrence` structure through the three setup
  types `(TypedOccurrenceMap, FillerData, AmbientAttachmentData)`,
  honoring the manuscript's L587/L591/L605 separation while reusing
  the cycle-4 record. Filler and ambient-attachment data are taken
  as `PUnit` because the cycle-4 `Occurrence` already bundles its
  own `ctx` and `θ`. -/
def ofFoundations {D : PrimitiveInterfaceData.{u}} (Dc : Doctrine D)
    (aux : BridgeAuxiliaryData Dc) : RewriteCalculusSetup.{u+1} where
  Slot := ULift.{u+1, u} D.P0
  Sort_ := ULift.{u+1, u} (Foundations.Sort_ D)
  Cirquent := ULift.{u+1, u} (Foundations.ExprCirquent Dc.sig)
  Goal := ULift.{u+1, u} (Foundations.Goal Dc.sig)
  State := Foundations.State Dc.sig
  goalOf := fun S => ULift.up S.goal
  OperationSymbol := ULift.{u+1, u} Dc.sig.Op
  RewriteScheme := ULift.{u+1, u} Dc.R_index
  admissible := fun i S =>
    decide (Dc.admissible i.down ⟨S.goal, PUnit⟩)
  TypedOccurrenceMap := fun i G =>
    ULift.{u+1, u} (Foundations.Occurrence Dc (Dc.R i.down) G.down)
  FillerData := fun _ _ => PUnit
  AmbientAttachmentData := fun _ _ => PUnit
  Carrier := aux.Carrier
  carrier := aux.carrier
  sanctionedByPatternAdmissionGate := fun c i G occ =>
    aux.sanctionedByPatternAdmissionGate c i.down G.down occ.down
  SupportData := fun i G => aux.SupportData i.down G.down
  consumes := fun supp => aux.consumes supp
  exports := fun supp => aux.exports supp
  ReplayCertificate := fun i S => aux.ReplayCertificate i.down S
  BoundaryObject := aux.BoundaryObject
  boundaryOf := aux.boundaryOf
  RefinedInterface := aux.RefinedInterface
  GluingWitness := aux.GluingWitness
  attachmentCompatible := aux.attachmentCompatible
  exposeBoundaryUnderSinkDeletion := aux.exposeBoundaryUnderSinkDeletion
  glueBoundary := aux.glueBoundary
  GeometricRewriteRule := aux.GeometricRewriteRule
  sinkDeletionGeometricRule := aux.sinkDeletionGeometricRule

/-! ### Witness theorems

These `rfl`-witnesses make the bridge's faithfulness explicit at
the type level. They are the "explicitly proved equivalent
reformulation" clauses of the strict anti-impersonation standard. -/

/-- The bridge's `Goal` is `ULift` of the foundations' `Goal`. -/
theorem ofFoundations_goal_eq {D : PrimitiveInterfaceData.{u}}
    (Dc : Doctrine D) (aux : BridgeAuxiliaryData Dc) :
    (ofFoundations Dc aux).Goal = ULift.{u+1, u} (Foundations.Goal Dc.sig) := rfl

/-- The bridge's `Sort_` is `ULift` of the foundations' `Sort_`. -/
theorem ofFoundations_sort_eq {D : PrimitiveInterfaceData.{u}}
    (Dc : Doctrine D) (aux : BridgeAuxiliaryData Dc) :
    (ofFoundations Dc aux).Sort_ = ULift.{u+1, u} (Foundations.Sort_ D) := rfl

/-- The bridge's `Cirquent` is `ULift` of the foundations'
`ExprCirquent`. -/
theorem ofFoundations_cirquent_eq {D : PrimitiveInterfaceData.{u}}
    (Dc : Doctrine D) (aux : BridgeAuxiliaryData Dc) :
    (ofFoundations Dc aux).Cirquent =
      ULift.{u+1, u} (Foundations.ExprCirquent Dc.sig) := rfl

/-- The bridge's `State` is the foundations' `State` directly
(already at universe `u+1`). -/
theorem ofFoundations_state_eq {D : PrimitiveInterfaceData.{u}}
    (Dc : Doctrine D) (aux : BridgeAuxiliaryData Dc) :
    (ofFoundations Dc aux).State = Foundations.State Dc.sig := rfl

/-- The bridge's `RewriteScheme` is `ULift` of the doctrine's
index type. -/
theorem ofFoundations_rewriteScheme_eq {D : PrimitiveInterfaceData.{u}}
    (Dc : Doctrine D) (aux : BridgeAuxiliaryData Dc) :
    (ofFoundations Dc aux).RewriteScheme =
      ULift.{u+1, u} Dc.R_index := rfl

/-- The bridge's `TypedOccurrenceMap i G` is `ULift` of the
foundations' `Occurrence Dc (Dc.R i.down) G.down`. -/
theorem ofFoundations_typedOccurrenceMap_eq {D : PrimitiveInterfaceData.{u}}
    (Dc : Doctrine D) (aux : BridgeAuxiliaryData Dc)
    (i : ULift.{u+1, u} Dc.R_index)
    (G : ULift.{u+1, u} (Foundations.Goal Dc.sig)) :
    (ofFoundations Dc aux).TypedOccurrenceMap i G =
      ULift.{u+1, u} (Foundations.Occurrence Dc (Dc.R i.down) G.down) := rfl

end RealObjects
end LayerB
end TraceCalc
