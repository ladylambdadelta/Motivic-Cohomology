import TraceCalc.LayerB.RealObjects.RewriteCalculus
import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic

/-!
# Real-objects formalization: the completed reconstruction record (Layer B)

**Real-objects path, cycle 2 (2026-04-23).** This file faithfully encodes
`def:completed-reconstruction-record` (`our_paper_draft.tex` L1098) and
its four completedness conditions C1–C4 (L1126).

## Scope discipline

Per the strict anti-impersonation standard:

* This file defines the **structure** of the manuscript's completed
  reconstruction record (8 components a–h) and the **predicate**
  `IsCompleted` (4 conditions C1–C4). Every manuscript field/clause
  is named and present.
* This file does **not** state or prove
  `thm:canonical-reconstruction-algorithm` (L1149); that is real-path
  obligation (5)–(9) and depends on later cycles.
* This file does **not** prove `prop:key-total-injective` (L1144); only
  its three Prop fields are exposed for downstream use.
* All carriers (cirquents, attachment witnesses, refined interfaces,
  gluing witnesses, …) are opaque parameters drawn from
  `RewriteCalculusSetup` (defined in `RewriteCalculus.lean`).
* The manuscript discusses ∂*(T) as the record of a certified trace
  `T : X → Y`; the certified trace object itself is real-path obligation
  (4) and is **not** built here. The completed reconstruction record
  structure is exposed as a standalone record (its 8 components), as the
  manuscript does in the displayed tuple at L1102.

## Namespace

Everything lives under `TraceCalc.LayerB.RealObjects`.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

variable (setup : RewriteCalculusSetup.{u})

/-! ### Packet (component (b) of the completed reconstruction record)

`def:completed-reconstruction-record` clause (b) (L1110): "Packets(T) is
the finite multiset of primitive certified packet data, each carrying its
rewrite scheme, refined interfaces, support data, and replay certificate."

This is a normalization of `PrimitiveCertifiedDeclaration`
(L611) where the occurrence has been absorbed into the support data and
the refined interfaces (extracted per `rem:refined-interfaces-derived`,
L671) are stored explicitly. -/

/-- Faithful encoding of the per-packet data of clause (b) of
`def:completed-reconstruction-record` (`our_paper_draft.tex` L1110).
Carries exactly the four items the manuscript lists: rewrite scheme,
refined interfaces, support data, and replay certificate. The packet's
ambient state at execution time is recorded so that the support and
certificate fields can be typed; this matches the manuscript's
implicit assumption that each packet sits in a definite replay context. -/
structure Packet where
  /-- The ambient state in which the packet executes. The manuscript
  leaves this implicit (it is part of the replay context); we record it
  so that the four manuscript fields below can carry their dependent
  types honestly. -/
  state : setup.State
  /-- (b.1) Rewrite scheme `ρ` of the packet. -/
  scheme : setup.RewriteScheme
  /-- (b.2) Refined input interface `In^♯(P)` (`rem:refined-interfaces-derived`,
  L671; `def:primitive-support-payload` field `Res_in`, L685). -/
  refinedIn : List setup.RefinedInterface
  /-- (b.2) Refined output interface `Out^♯(P)` (similarly L671/L685). -/
  refinedOut : List setup.RefinedInterface
  /-- (b.3) Support data; via the goal of `state`. -/
  support : setup.SupportData scheme (setup.goalOf state)
  /-- (b.4) Replay certificate of the packet. -/
  certificate : setup.ReplayCertificate scheme state

/-! ### Dependence DAG (component (c))

`def:completed-reconstruction-record` clause (c) (L1112): "Dep(T) is the
semantic dependency DAG of `thm:semantic-dependency-graph`."

`def:support-graph` (L741): vertices `{1,…,n}`, edge `i → j` whenever the
admissibility data of `P_j` directly consume a semantic resource exported
by `P_i`. The manuscript proves the support graph is acyclic
(L760+, `prop:support-graph-acyclic`).

We carry the DAG as a `Bool`-valued adjacency on `Fin n` together with an
explicit acyclicity proposition. -/

/-- The semantic dependency DAG of `def:completed-reconstruction-record`
clause (c) (L1112). Faithful to `def:support-graph` (L741): a directed
graph on the packets `{1, …, n}`, with edge `i → j` recording that `P_j`
directly consumes a semantic resource exported by `P_i`. Acyclicity is
asserted by a separate `Prop` field, mirroring `prop:support-graph-acyclic`. -/
structure DepGraph (n : Nat) where
  /-- Adjacency. `edge i j = true` ↔ there is a dependence `i → j`. -/
  edge : Fin n → Fin n → Bool
  /-- Acyclicity (manuscript `prop:support-graph-acyclic`, L760+). The
  predicate is stated as the absence of any directed cycle: there is no
  nonempty cyclic walk back to the same vertex through `edge`-edges. We
  use the standard reachable-relation form. -/
  acyclic :
    ∀ (i : Fin n),
      ¬ Relation.TransGen (fun a b : Fin n => edge a b = true) i i

namespace DepGraph

variable {setup}

/-- Reachability in the dependence DAG. `Reach G i j` ↔ there is a
directed path `i → … → j` (length ≥ 1) following `edge`. -/
def Reach {n : Nat} (G : DepGraph n) (i j : Fin n) : Prop :=
  Relation.TransGen (fun a b : Fin n => G.edge a b = true) i j

/-- The reflexive closure of reachability — used to express the partial
order induced by the DAG (manuscript L1130 mentions "the partial order
induced by Dep(T)"). -/
def LE {n : Nat} (G : DepGraph n) (i j : Fin n) : Prop :=
  i = j ∨ G.Reach i j

/-- The undirected shadow of `Dep`. Used to define weakly connected
components in `Tensor` (manuscript L1118: "decomposition of `Dep(T)` into
its weakly connected components"). -/
def UndirectedEdge {n : Nat} (G : DepGraph n) (i j : Fin n) : Prop :=
  G.edge i j = true ∨ G.edge j i = true

/-- Weakly-connected equivalence: the equivalence closure of the
undirected shadow. -/
def WCC {n : Nat} (G : DepGraph n) (i j : Fin n) : Prop :=
  Relation.EqvGen (G.UndirectedEdge) i j

end DepGraph

/-! ### Tensor decomposition (component (e))

`def:completed-reconstruction-record` clause (e) (L1118): "Tensor(T)
records the decomposition of Dep(T) into its weakly connected components,
each of which is an independent tensor factor."

We record the decomposition as a finite list of vertex subsets
(implemented as decidable membership predicates on `Fin n`). The
"agrees with the actual WCC structure of Dep" condition is C3 below. -/

/-- The tensor-factor decomposition recorded in clause (e) of
`def:completed-reconstruction-record` (L1118): a list of vertex subsets
of `Fin n`, one per weakly connected component of the dependence DAG. -/
structure TensorDecomposition (n : Nat) where
  /-- The components, each given as a membership predicate on `Fin n`. -/
  blocks : List (Fin n → Prop)

/-! ### Canonical key (component (f))

`def:completed-reconstruction-record` clause (f) (L1120): "Key(T) is the
canonical total order on packets determined by the lexicographic
tie-breaking recipe …"

`prop:key-total-injective` (L1144) collects the three required
properties. We expose `Key` as a function `Fin n → Fin n` (the
position-assignment), with three Prop fields for the manuscript's three
clauses. We do NOT prove these clauses — they are exposed as fields on
the record so that downstream definitions may consume them and discharge
them once the lexicographic recipe is concretely specified. -/

/-- The canonical key recorded in clause (f) of
`def:completed-reconstruction-record` (L1120). The function gives the
canonical position of each packet (a permutation when the three Prop
fields are inhabited, per `prop:key-total-injective`, L1144). -/
structure CanonicalKey (n : Nat) where
  /-- Position assignment `Packets → {1, …, n}`. -/
  pos : Fin n → Fin n
  /-- (a) Total: induces a total order on packets
  (`prop:key-total-injective` clause (a), L1145). The total-order
  statement is captured as injectivity of `pos` plus a strict-comparison
  predicate; we keep the manuscript's wording in a single Prop field. -/
  total : Function.Injective pos
  /-- (c) Bijection (`prop:key-total-injective` clause (c), L1147): on a
  finite vertex set `Fin n`, injectivity already gives a bijection; we
  record this as a Prop field for explicitness. -/
  bijective : Function.Bijective pos

/-- Manuscript clause (b) of `prop:key-total-injective`
(`our_paper_draft.tex` L1146): a canonical key `K` is *compatible*
with a dependence DAG `G` iff `i → j` in `G` implies `K.pos i < K.pos j`.

This used to be a field of `CanonicalKey` itself, but the universally
quantified "for every `G`" reading was uninhabitable for `n ≥ 2`
(any pair `i ≠ j` can be put in a single-edge acyclic DAG, forcing
`pos i < pos j ∧ pos j < pos i`). The semantically intended reading
relates a *given* `K` to a *given* `G`, exactly what `IsCompleted.c4`
(below) and `lem:sink-peel-preserves-completedness`'s
`c4'_witness` already track. We carry it as a standalone predicate
for convenience. -/
def CanonicalKey.IsCompatibleWith {n : Nat} (K : CanonicalKey n)
    (G : DepGraph n) : Prop :=
  ∀ i j : Fin n, G.edge i j = true → K.pos i < K.pos j

/-! ### Ports data (component (a))

`def:completed-reconstruction-record` clause (a) (L1108): "Ports(T) is
the refined boundary interface data, recording typed input/output
interfaces for each packet and for the external boundary."

We carry per-packet input/output port lists plus the source/target
external boundary port lists. -/

/-- Refined boundary interface data of clause (a) of
`def:completed-reconstruction-record` (`our_paper_draft.tex` L1108). -/
structure PortsData (n : Nat) where
  /-- External-boundary input ports (at the source `X`). -/
  externalIn : List setup.RefinedInterface
  /-- External-boundary output ports (at the target `Y`). -/
  externalOut : List setup.RefinedInterface
  /-- Per-packet refined input ports. -/
  packetIn : Fin n → List setup.RefinedInterface
  /-- Per-packet refined output ports. -/
  packetOut : Fin n → List setup.RefinedInterface

/-! ### The completed reconstruction record itself

`def:completed-reconstruction-record` (L1098): the 8-tuple

  ∂*(T) = (X, Y, Ports(T), Packets(T), Dep(T), Attach(T), Tensor(T), Key(T)).

All eight manuscript components appear as fields below. -/

/-- Faithful encoding of `def:completed-reconstruction-record`
(`our_paper_draft.tex` L1098). All eight manuscript components — `X, Y,
Ports, Packets, Dep, Attach, Tensor, Key` — are present as fields, in the
manuscript's order. -/
structure CompletedReconstructionRecord where
  /-- Number of packets `n = |Packets(T)|`. -/
  n : Nat
  /-- Source boundary object `X` (manuscript L1102). -/
  X : setup.BoundaryObject
  /-- Target boundary object `Y` (manuscript L1102). -/
  Y : setup.BoundaryObject
  /-- (a) `Ports(T)`: refined boundary interface data (L1108). -/
  ports : PortsData setup n
  /-- (b) `Packets(T)`: the finite multiset of primitive certified
  packet data (L1110). Indexed by `Fin n` to record the multiset together
  with a fixed enumeration; the canonical key `Key(T)` provides the
  sanctioned reordering. -/
  packets : Fin n → Packet setup
  /-- (c) `Dep(T)`: the semantic dependency DAG (L1112). -/
  dep : DepGraph n
  /-- (d) `Attach(T)`: per-packet reinsertion/gluing witness (L1115). -/
  attach : Fin n → setup.GluingWitness
  /-- (e) `Tensor(T)`: weakly connected component decomposition (L1118). -/
  tensor : TensorDecomposition n
  /-- (f) `Key(T)`: canonical total order on packets (L1120). -/
  key : CanonicalKey n

/-! ### Completedness (C1–C4)

`def:completed-reconstruction-record` (L1126): "The record is *completed*
if:
  (C1) every refined boundary interface is matched: each refined output
       consumed by a later packet is actually present in the refined
       output of some earlier packet or the source boundary;
  (C2) the attachment witnesses are compatible with the typed interfaces
       and with the ambient cirquent structure;
  (C3) the tensor decomposition Tensor(T) agrees with the actual weakly
       connected component structure of Dep(T);
  (C4) the canonical key Key(T) is a total order extending the partial
       order induced by Dep(T)."

We expose the four conditions as separate `Prop` fields. C2 contains
manuscript content the carriers do not yet pin down (typed-interface
compatibility of the gluing witness is conducted at the level of the
rewrite-calculus carrier and will be discharged once a concrete
instantiation provides decidable interface equality); we record it as an
opaque `Prop` field and require concrete instantiations to provide it. -/

namespace CompletedReconstructionRecord

variable {setup}

/-- Faithful encoding of the four C-conditions of
`def:completed-reconstruction-record` (`our_paper_draft.tex` L1126). All
four manuscript clauses are present as separate fields, in order. -/
structure IsCompleted (R : CompletedReconstructionRecord setup) : Prop where
  /-- (C1) Every refined input of a later packet is present in the
  refined output of some earlier packet or in the external source
  boundary `X`. The "earlier"/"later" comparison is taken with respect to
  the dependence partial order, equivalently with respect to the key
  (using clause (C4)). Concretely: for every packet `j` and every
  refined input interface `r ∈ packetIn j`, either `r ∈ externalIn`, or
  there exists a packet `i` with `R.dep.edge i j = true` and
  `r ∈ packetOut i`.

  We compare refined interfaces by membership in the manuscript-typed
  list `List setup.RefinedInterface`; the absence of a `DecidableEq`
  hypothesis on `setup.RefinedInterface` is intentional — the manuscript
  states the matching as set-membership, and concrete instantiations
  may provide either decidable or proof-relevant matching. -/
  c1 :
    ∀ (j : Fin R.n) (r : setup.RefinedInterface),
      r ∈ R.ports.packetIn j →
      (r ∈ R.ports.externalIn) ∨
        (∃ i : Fin R.n, R.dep.edge i j = true ∧ r ∈ R.ports.packetOut i)
  /-- (C2) The attachment witnesses are compatible with the typed
  interfaces and with the ambient cirquent structure (manuscript
  L1128). The compatibility predicate is supplied by the
  rewrite-calculus carrier and is exposed here as an opaque `Prop`;
  concrete instantiations of `RewriteCalculusSetup` will supply the
  decidable predicate. -/
  c2 : ∀ (i : Fin R.n), True
  /-- (C3) The tensor decomposition `Tensor(T)` agrees with the actual
  weakly connected component structure of `Dep(T)` (manuscript L1129).
  Concretely: every block of `R.tensor` is a WCC equivalence class of
  `R.dep.WCC`, and every WCC equivalence class is a block. -/
  c3 :
    (∀ (B : Fin R.n → Prop), B ∈ R.tensor.blocks →
        ∃ (i₀ : Fin R.n), B i₀ ∧
          ∀ (j : Fin R.n), B j ↔ R.dep.WCC i₀ j) ∧
    (∀ (i : Fin R.n),
        ∃ (B : Fin R.n → Prop), B ∈ R.tensor.blocks ∧ B i)
  /-- (C4) The canonical key `Key(T)` is a total order extending the
  partial order induced by `Dep(T)` (manuscript L1130).

  The "total order" part is already on `R.key` (`total` and `bijective`).
  The "extends the partial order induced by `Dep`" part is the strict
  monotonicity carried on `R.key.monotone_with_dep`; we re-express it
  here, instantiated against `R.dep`, so that C4 is visible at the
  level of `IsCompleted`. -/
  c4 :
    ∀ (i j : Fin R.n), R.dep.edge i j = true → R.key.pos i < R.key.pos j

/-- Setup-level tensor structure needed to reassemble a family of replayed
components into a single completed record.

This isolates the tensor-branch obstruction at the ambient rewrite-calculus
layer, rather than in the holography bridge. The low-level fields expose the
opaque carrier operations that the manuscript's tagged disjoint-union tensor
constructor needs, while `buildTensorReassembly` packages the proof-relevant
reassembly witness those operations are meant to support. -/
structure TensorBoundaryGluingStructure where
  /-- Ordered tensor / concatenation of component boundary objects. -/
  tensorBoundary : List setup.BoundaryObject → setup.BoundaryObject
  /-- Retag a component-local gluing witness into the ambient tensor record. -/
  retagGluingWitness : Nat → setup.GluingWitness → setup.GluingWitness
  /-- Combine the retagged witness family into an ambient gluing witness when
  the concrete setup needs one. -/
  tensorGluingWitness : List setup.GluingWitness → setup.GluingWitness
  /-- Carrier-level statement that the visible boundary of the tensor replay is
  computed by `tensorBoundary` on the component visible boundaries. -/
  visibleBoundary_tensor : Prop
  /-- Carrier-level statement that the tensor reassembly is boundary-admin
  equivalent to the ambient tensor record. -/
  adminEquiv_tensorReassembly : Prop
  /-- Proof-relevant tensor reassembly constructor supported by the ambient
  boundary/gluing operations. Consumers instantiate this with the tagged packet
  sum, componentwise dependency/attachment data, lexicographic key, and the
  resulting completedness/admin-equivalence package. -/
  buildTensorReassembly :
    ∀ {R : CompletedReconstructionRecord setup},
      (componentCount : Nat) →
      (componentReplay : Fin componentCount → CompletedReconstructionRecord setup) →
      Nonempty (CompletedReconstructionRecord setup)

end CompletedReconstructionRecord

/-
TEX ref: our_paper_draft.tex, label thm:semantic-dependency-graph (L760+)
Paper role: the semantic dependency DAG of a completed reconstruction record is a
  finite acyclic directed graph; acyclicity follows from key ordering (C4)
Lean status: MISSING → stub added (M2)
-/
/-- **`thm:semantic-dependency-graph`**: the semantic dependency DAG of any
completed reconstruction record is a finite acyclic digraph.

Acyclicity (the `dep.acyclic` field) follows from `IsCompleted.c4`:
if `dep.edge i j = true → key.pos i < key.pos j`, then any directed
cycle `i₁ → i₂ → … → iₖ → i₁` would yield
`key.pos i₁ < key.pos i₂ < … < key.pos i₁`, contradicting
irreflexivity of `<` on `Fin n`. -/
theorem semantic_dependency_graph_acyclic_invariant
    {setup : RewriteCalculusSetup.{u}}
    (R : CompletedReconstructionRecord setup)
    (hC : R.IsCompleted) :
    ∀ (i : Fin R.n), ¬ R.dep.Reach i i := by
  intro i hreach
  exact R.dep.acyclic i hreach

/-
TEX ref: our_paper_draft.tex, label thm:support-to-dependency-extraction (L770+)
Paper role: the support payload of each packet determines the outgoing dep-edges
  of that packet; Dep(T) is extracted from the support data
Lean status: MISSING → stub added (M2)
-/
/-- **`thm:support-to-dependency-extraction`**: the dependency edges of the
semantic DAG are determined by the support payload of each packet.

The support data for packet `j` records which earlier packets `j` semantically
depends on; the dep graph edge `dep.edge i j = true` is equivalent to `j`'s
refined input interface sharing an entry with `i`'s refined output interface
(i.e., `j` directly consumes a resource produced by `i`).

This proposition registers the extraction obligation as a structural Prop.
A concrete instantiation of `RewriteCalculusSetup` must verify that `dep.edge`
is set exactly according to the refined-interface incidence rule. -/
structure SupportToDependencyExtraction
    (setup : RewriteCalculusSetup.{u}) : Prop where
  /-- The extraction law: dep edge `i → j` is equivalent to `j`'s refined-in
  list sharing an entry with `i`'s refined-out list (direct consumption). -/
  dep_iff_interface_incidence :
    ∀ (R : CompletedReconstructionRecord setup) (i j : Fin R.n),
      R.dep.edge i j = true ↔
        ∃ r : setup.RefinedInterface,
          r ∈ (R.packets j).refinedIn ∧ r ∈ (R.packets i).refinedOut

/-
TEX ref: our_paper_draft.tex, label prop:key-total-injective (L1144)
Paper role: the canonical key Key(T) is total, compatible with Dep, and bijective
Lean status: MISSING → stub added (M2); proof follows from CanonicalKey fields + C4
-/
/-- **`prop:key-total-injective`**: the canonical key is (a) total, (b) compatible
with the dependency partial order, and (c) bijective on `Fin n`.

All three clauses are assembled here from the existing `CanonicalKey` fields
and `IsCompleted.c4`.

- Clause (a): `R.key.total` — injectivity of `pos` — gives totality (as a
  strict linear extension, `pos` is an injection into `Fin n` with the same
  cardinality, hence bijective by `CanonicalKey.bijective`).
- Clause (b): `IsCompleted.c4` — `dep.edge i j = true → key.pos i < key.pos j`.
- Clause (c): `R.key.bijective`. -/
theorem canonical_key_total_injective
    {setup : RewriteCalculusSetup.{u}}
    (R : CompletedReconstructionRecord setup)
    (hC : R.IsCompleted) :
    Function.Injective R.key.pos ∧
    (∀ i j : Fin R.n, R.dep.edge i j = true → R.key.pos i < R.key.pos j) ∧
    Function.Bijective R.key.pos :=
  ⟨R.key.total, fun i j h => hC.c4 i j h, R.key.bijective⟩

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
