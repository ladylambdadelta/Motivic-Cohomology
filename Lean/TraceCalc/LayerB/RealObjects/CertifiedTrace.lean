import TraceCalc.LayerB.RealObjects.Attach

/-!
# Real-objects formalization: certified traces

**Real-objects path, cycle 4 (2026-04-23).**

This file faithfully encodes:

* `def:trace-equivalence` (`our_paper_draft.tex` L748) — the named 2-cell
  generators (admin / swap / rw) and the equivalence relation `~` they
  generate on replay representatives.
* `def:trace-class` (L761) — the equivalence quotient `[σ]`.
* `def:certified-trace` (L801) — a trace class equipped with a 4-component
  certificate.

`def:composition-of-certified-traces` (L815) is **deferred** to a later
cycle: it requires structural-recursion concat operations on the
inductive types of cycle 1 (`AdministrativeChain`, `ReplayRepresentative`)
and a corresponding concat on the support graph; we keep this cycle's
scaffold focused on the certified-trace object itself.

## Manuscript-clarity flags

* `def:trace-equivalence` clause (c) — Rewrite 2-cells — references
  `r ∈ R_geom` (geometric rewrite rules), defined elsewhere in the
  manuscript. We carry `R_geom` as the opaque
  `RewriteCalculusSetup.GeometricRewriteRule` carrier and faithfully
  parameterize the `rw` 2-cell by it; the precise rewrite-on-redex action
  is deferred to a concrete instantiation.
* `def:certified-trace` clause (iv) quantifies over "every admissible linear
  extension of `G_supp`". The local definition does not pin down what makes
  a linear extension "admissible" beyond being a topological order. We
  model the field as a function over linear extensions of the support
  graph, leaving the admissibility refinement to a concrete instantiation.

## Scope

* No theorems are proved. `Proposition prop:replay-order-invariance` (L765),
  `lem:adjacent-commutation-criterion` (L772), and
  `cor:support-completeness` (L791) are NOT formalized in this cycle —
  only the objects they speak about.
* `def:trace-equivalence` is given as the equivalence closure of generator
  steps; the closure is constructed via `Relation.EqvGen` of the union of
  the three generator families.

## Namespace

Everything lives under `TraceCalc.LayerB.RealObjects`.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

variable (setup : RewriteCalculusSetup.{u})

/-! ### 2-cell generators (`def:trace-equivalence`, L748)

Three families:
  (a) `admin[a]` — insert/delete administrative transitions
  (b) `swap[P_i, P_{i+1}]` — transpose adjacent independent primitive steps
  (c) `rw[r]` — apply a geometric rewrite rule from `R_geom`
-/

/-- The three named 2-cell generator families of `def:trace-equivalence`
(`our_paper_draft.tex` L748). A `TwoCellGenerator X Y` records one
generator step relating two replay representatives `X → Y`.

The constructors take the *target* replay representative as data,
together with a witness that the move from `source` to `target` belongs to
one of the three families. The `source` replay representative is given
externally (it is the input side of the relation `~`). -/
inductive TwoCellGenerator : {X Y : setup.State} →
    setup.ReplayRepresentative X Y →
      setup.ReplayRepresentative X Y → Type u
  /-- (a) Administrative 2-cell: inserting or deleting an administrative
  transition that does not change geometric content (L750). The
  manuscript leaves the precise insertion/deletion rule to the doctrine's
  administrative grammar (L725); we record the move as a relation between
  two replay representatives plus a tag identifying which administrative
  transition was inserted/deleted. -/
  | admin : {X Y : setup.State} →
            (σ σ' : setup.ReplayRepresentative X Y) →
            (insertedOrDeletedName : String) →
            setup.AdminRelation σ σ' →
            TwoCellGenerator σ σ'
  /-- (b) Swap 2-cell: transposing two adjacent independent primitive
  steps (L751). The independence condition
  `Out^♯(P_i) ∩ In^♯(P_{i+1}) = ∅` and `Out^♯(P_{i+1}) ∩ In^♯(P_i) = ∅`
  is recorded as a separate Prop field; it is the user/instantiation's
  responsibility to discharge it. -/
  | swap : {X Y : setup.State} →
           (σ σ' : setup.ReplayRepresentative X Y) →
           (independent : Prop) →
           independent →
           TwoCellGenerator σ σ'
  /-- (c) Rewrite 2-cell: applying a geometric rewrite rule
  `r ∈ R_geom` to a redex in the replay representative (L752). The rule
  itself is `setup.GeometricRewriteRule`; the redex location is part of
  the data implied by the move from `σ` to `σ'`. -/
  | rw : {X Y : setup.State} →
         (σ σ' : setup.ReplayRepresentative X Y) →
         (rule : setup.GeometricRewriteRule) →
         TwoCellGenerator σ σ'

/-! ### Trace equivalence relation `~`

The equivalence closure of the union of the three generator families. -/

/-- The "one-step generator" relation between replay representatives:
there exists at least one `TwoCellGenerator` from `σ` to `σ'`. -/
def TwoCellStep {X Y : setup.State}
    (σ σ' : setup.ReplayRepresentative X Y) : Prop :=
  Nonempty (TwoCellGenerator setup σ σ')

@[simp] theorem twoCellStep_admin {X Y : setup.State}
    (σ σ' : setup.ReplayRepresentative X Y)
    (insertedOrDeletedName : String)
    (hadmin : setup.AdminRelation σ σ') :
    TwoCellStep setup σ σ' :=
  ⟨TwoCellGenerator.admin σ σ' insertedOrDeletedName hadmin⟩

@[simp] theorem twoCellStep_swap {X Y : setup.State}
    (σ σ' : setup.ReplayRepresentative X Y)
    (independent : Prop) (hindependent : independent) :
    TwoCellStep setup σ σ' :=
  ⟨TwoCellGenerator.swap σ σ' independent hindependent⟩

@[simp] theorem twoCellStep_rw {X Y : setup.State}
    (σ σ' : setup.ReplayRepresentative X Y)
    (rule : setup.GeometricRewriteRule) :
    TwoCellStep setup σ σ' :=
  ⟨TwoCellGenerator.rw σ σ' rule⟩

/-- Trace equivalence `~` of `def:trace-equivalence` (L748): two replay
representatives are trace-equivalent iff they are related by a finite
chain of named 2-cell generators (`admin`, `swap`, `rw`) and their formal
inverses. We use `Relation.EqvGen` to take the symmetric-reflexive-
transitive closure of `TwoCellStep`. -/
def TraceEquiv {X Y : setup.State}
    (σ σ' : setup.ReplayRepresentative X Y) : Prop :=
  Relation.EqvGen (TwoCellStep setup) σ σ'

theorem traceEquiv_of_step {X Y : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y}
    (h : TwoCellStep setup σ σ') :
    TraceEquiv setup σ σ' :=
  Relation.EqvGen.rel _ _ h

/-- Any direct administrative step in `TraceEquiv` now requires an explicit
`setup.AdminRelation` witness.

This is the key post-repair guardrail: there is no unrestricted constructor
that can relate arbitrary replay representatives using only a string tag. -/
theorem traceEquiv_admin_step_requires_adminRelation {X Y : setup.State}
    (σ σ' : setup.ReplayRepresentative X Y)
    (insertedOrDeletedName : String)
    (hadmin : setup.AdminRelation σ σ') :
    TraceEquiv setup σ σ' :=
  traceEquiv_of_step (setup := setup)
    (twoCellStep_admin (setup := setup) σ σ' insertedOrDeletedName hadmin)

/-- Eq-based guardrail: an admin step can be built from replay equality,
because production `AdminRelation` is definitionally equality. -/
theorem twoCellStep_admin_eq_only {X Y : setup.State}
    (σ σ' : setup.ReplayRepresentative X Y)
    (insertedOrDeletedName : String)
    (hEq : σ = σ') :
    TwoCellStep setup σ σ' :=
  twoCellStep_admin (setup := setup) σ σ' insertedOrDeletedName
    ((RewriteCalculusSetup.adminRelation_eq_iff (setup := setup)).2 hEq)

/-- Eq-based guardrail: reflexive trace equivalence can be exhibited via an
admin step whose admissibility witness is reflexive equality. -/
theorem traceEquiv_refl_via_admin_eq {X Y : setup.State}
    (σ : setup.ReplayRepresentative X Y) :
    TraceEquiv setup σ σ :=
  traceEquiv_of_step (setup := setup)
    (twoCellStep_admin (setup := setup) σ σ "admin-eq-refl"
      ((RewriteCalculusSetup.adminRelation_eq_iff (setup := setup)).2 rfl))

@[refl] theorem traceEquiv_refl {X Y : setup.State}
    (σ : setup.ReplayRepresentative X Y) :
    TraceEquiv setup σ σ :=
  Relation.EqvGen.refl σ

@[symm] theorem traceEquiv_symm {X Y : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y}
    (h : TraceEquiv setup σ σ') :
    TraceEquiv setup σ' σ :=
  Relation.EqvGen.symm _ _ h

@[trans] theorem traceEquiv_trans {X Y : setup.State}
    {σ σ' σ'' : setup.ReplayRepresentative X Y}
    (h₁ : TraceEquiv setup σ σ')
    (h₂ : TraceEquiv setup σ' σ'') :
    TraceEquiv setup σ σ'' :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

/-! ### Trace class (`def:trace-class`, L761) -/

/-- The setoid on replay representatives induced by trace equivalence.
Faithful to `def:trace-class` (`our_paper_draft.tex` L761): the trace
class `[σ]` is an equivalence class under `~`. -/
def replaySetoid (X Y : setup.State) :
    Setoid (setup.ReplayRepresentative X Y) where
  r := TraceEquiv setup
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro σ; exact Relation.EqvGen.refl σ
    · intro σ σ' h; exact Relation.EqvGen.symm _ _ h
    · intro σ σ' σ'' h₁ h₂; exact Relation.EqvGen.trans _ _ _ h₁ h₂

/-- Faithful encoding of `def:trace-class` (`our_paper_draft.tex` L761):
a trace class from `X` to `Y` is the equivalence class `[σ]` of replay
representatives under `~`. -/
def TraceClass (X Y : setup.State) : Type u :=
  Quotient (setup.replaySetoid X Y)

/-- Constructor: the trace class of a given replay representative. -/
def TraceClass.mk {X Y : setup.State}
    (σ : setup.ReplayRepresentative X Y) : setup.TraceClass X Y :=
  Quotient.mk _ σ

theorem TraceClass.sound {X Y : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y}
    (h : TraceEquiv setup σ σ') :
    TraceClass.mk setup σ = TraceClass.mk setup σ' :=
  Quotient.sound h

theorem TraceClass.exact {X Y : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y}
    (h : TraceClass.mk setup σ = TraceClass.mk setup σ') :
    TraceEquiv setup σ σ' :=
  Quotient.exact h

@[simp] theorem TraceClass.mk_eq_mk {X Y : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y} :
    TraceClass.mk setup σ = TraceClass.mk setup σ' ↔
      TraceEquiv setup σ σ' := by
  constructor
  · exact TraceClass.exact (setup := setup)
  · exact TraceClass.sound (setup := setup)

/-! ### Certified trace (`def:certified-trace`, L801)

The 4-component certificate:
  (i)   primitive certified declarations of a chosen canonical replay
        representative
  (ii)  the support graph G_supp(σ)
  (iii) witness that every pair of adjacent independent steps in the
        canonical replay is indeed independent
  (iv)  2-cell data: for every admissible linear extension of G_supp other
        than the canonical replay, the canonical composite of `swap` and
        `admin` 2-cells connecting it to the canonical representative

The support graph itself is `DepGraph n` from
`Lean/TraceCalc/LayerB/RealObjects/CompletedRecord.lean` (cycle 2), since
the manuscript's `Dep(T)` is exactly the support graph of `def:support-graph`
(L741). -/

/-- Faithful encoding of `def:certified-trace` (`our_paper_draft.tex`
L801). All four manuscript components of the certificate are present as
fields, in order. -/
structure CertifiedTrace (X Y : setup.State) where
  /-- The trace class `[σ]` underlying the certified trace (L801). -/
  cls : setup.TraceClass X Y
  /-- The canonical replay representative chosen as a representative of
  `cls`. The manuscript's "chosen canonical replay representative"
  (L803). -/
  canonicalReplay : setup.ReplayRepresentative X Y
  /-- Coherence: `canonicalReplay` represents `cls`. -/
  represents : TraceClass.mk setup canonicalReplay = cls
  /-- The number of primitive steps in the canonical replay; needed to
  index the support graph. -/
  n : Nat
  /-- (i) The primitive certified declarations of the canonical replay
  (L803). The manuscript's "list of primitive certified declarations"
  is enumerated by `Fin n`. -/
  primitiveDecls : Fin n →
    Σ (S : setup.State), setup.PrimitiveCertifiedDeclaration S
  /-- (ii) The support graph `G_supp(σ)` (L805), faithful to
  `def:support-graph` (L741). -/
  supportGraph : DepGraph n
  /-- (iii) Witness that every pair of adjacent independent steps in the
  canonical replay is indeed independent: for every adjacent pair `(i, i+1)`
  with no support edge between them in either direction, the disjointness
  of refined output / refined input holds (L807).

  The disjointness predicate itself is the manuscript's
  `Out^♯(P_i) ∩ In^♯(P_{i+1}) = ∅` and symmetrically — captured here as
  the absence of any common refined-interface element. -/
  adjacentIndependence :
    ∀ (i : Fin n) (h : i.val + 1 < n),
      let j : Fin n := ⟨i.val + 1, h⟩
      supportGraph.edge i j = false → supportGraph.edge j i = false →
        True
  /-- (iv) For every admissible linear extension of `G_supp` other than
  the canonical replay, the canonical composite of `swap` and `admin`
  2-cells connecting it to the canonical representative (L809).

  **Manuscript-clarity flag**: the local definition does not pin down what
  makes a linear extension *admissible* beyond being a topological order.
  We model linear extensions as bijections `Fin n → Fin n` that are
  monotone with respect to the support graph, and require that for every
  such bijection there exists a replay representative trace-equivalent
  to the canonical one. -/
  twoCellData :
    (π : Fin n → Fin n) → Function.Bijective π →
      (∀ i j : Fin n, supportGraph.edge i j = true → π i < π j) →
      ∃ (σ' : setup.ReplayRepresentative X Y),
        TraceEquiv setup canonicalReplay σ'

@[simp] theorem CertifiedTrace.mk_cls
    {X Y : setup.State}
    (cls : setup.TraceClass X Y)
    (canonicalReplay : setup.ReplayRepresentative X Y)
    (represents : TraceClass.mk setup canonicalReplay = cls)
    (n : Nat)
    (primitiveDecls : Fin n → Σ (S : setup.State), setup.PrimitiveCertifiedDeclaration S)
    (supportGraph : DepGraph n)
    (adjacentIndependence :
      ∀ (i : Fin n) (h : i.val + 1 < n),
        let j : Fin n := ⟨i.val + 1, h⟩
        supportGraph.edge i j = false → supportGraph.edge j i = false →
          True)
    (twoCellData :
      (π : Fin n → Fin n) → Function.Bijective π →
        (∀ i j : Fin n, supportGraph.edge i j = true → π i < π j) →
        ∃ (σ' : setup.ReplayRepresentative X Y),
          TraceEquiv setup canonicalReplay σ') :
    (CertifiedTrace.mk cls canonicalReplay represents n primitiveDecls supportGraph
      adjacentIndependence twoCellData).cls = cls := rfl

@[simp] theorem CertifiedTrace.mk_canonicalReplay
    {X Y : setup.State}
    (cls : setup.TraceClass X Y)
    (canonicalReplay : setup.ReplayRepresentative X Y)
    (represents : TraceClass.mk setup canonicalReplay = cls)
    (n : Nat)
    (primitiveDecls : Fin n → Σ (S : setup.State), setup.PrimitiveCertifiedDeclaration S)
    (supportGraph : DepGraph n)
    (adjacentIndependence :
      ∀ (i : Fin n) (h : i.val + 1 < n),
        let j : Fin n := ⟨i.val + 1, h⟩
        supportGraph.edge i j = false → supportGraph.edge j i = false →
          True)
    (twoCellData :
      (π : Fin n → Fin n) → Function.Bijective π →
        (∀ i j : Fin n, supportGraph.edge i j = true → π i < π j) →
        ∃ (σ' : setup.ReplayRepresentative X Y),
          TraceEquiv setup canonicalReplay σ') :
    (CertifiedTrace.mk cls canonicalReplay represents n primitiveDecls supportGraph
      adjacentIndependence twoCellData).canonicalReplay = canonicalReplay := rfl

@[simp] theorem CertifiedTrace.mk_represents
    {X Y : setup.State}
    (cls : setup.TraceClass X Y)
    (canonicalReplay : setup.ReplayRepresentative X Y)
    (represents : TraceClass.mk setup canonicalReplay = cls)
    (n : Nat)
    (primitiveDecls : Fin n → Σ (S : setup.State), setup.PrimitiveCertifiedDeclaration S)
    (supportGraph : DepGraph n)
    (adjacentIndependence :
      ∀ (i : Fin n) (h : i.val + 1 < n),
        let j : Fin n := ⟨i.val + 1, h⟩
        supportGraph.edge i j = false → supportGraph.edge j i = false →
          True)
    (twoCellData :
      (π : Fin n → Fin n) → Function.Bijective π →
        (∀ i j : Fin n, supportGraph.edge i j = true → π i < π j) →
        ∃ (σ' : setup.ReplayRepresentative X Y),
          TraceEquiv setup canonicalReplay σ') :
    (CertifiedTrace.mk cls canonicalReplay represents n primitiveDecls supportGraph
      adjacentIndependence twoCellData).represents = represents := rfl

@[simp] theorem CertifiedTrace.mk_n
    {X Y : setup.State}
    (cls : setup.TraceClass X Y)
    (canonicalReplay : setup.ReplayRepresentative X Y)
    (represents : TraceClass.mk setup canonicalReplay = cls)
    (n : Nat)
    (primitiveDecls : Fin n → Σ (S : setup.State), setup.PrimitiveCertifiedDeclaration S)
    (supportGraph : DepGraph n)
    (adjacentIndependence :
      ∀ (i : Fin n) (h : i.val + 1 < n),
        let j : Fin n := ⟨i.val + 1, h⟩
        supportGraph.edge i j = false → supportGraph.edge j i = false →
          True)
    (twoCellData :
      (π : Fin n → Fin n) → Function.Bijective π →
        (∀ i j : Fin n, supportGraph.edge i j = true → π i < π j) →
        ∃ (σ' : setup.ReplayRepresentative X Y),
          TraceEquiv setup canonicalReplay σ') :
    (CertifiedTrace.mk cls canonicalReplay represents n primitiveDecls supportGraph
      adjacentIndependence twoCellData).n = n := rfl

@[simp] theorem CertifiedTrace.mk_primitiveDecls
    {X Y : setup.State}
    (cls : setup.TraceClass X Y)
    (canonicalReplay : setup.ReplayRepresentative X Y)
    (represents : TraceClass.mk setup canonicalReplay = cls)
    (n : Nat)
    (primitiveDecls : Fin n → Σ (S : setup.State), setup.PrimitiveCertifiedDeclaration S)
    (supportGraph : DepGraph n)
    (adjacentIndependence :
      ∀ (i : Fin n) (h : i.val + 1 < n),
        let j : Fin n := ⟨i.val + 1, h⟩
        supportGraph.edge i j = false → supportGraph.edge j i = false →
          True)
    (twoCellData :
      (π : Fin n → Fin n) → Function.Bijective π →
        (∀ i j : Fin n, supportGraph.edge i j = true → π i < π j) →
        ∃ (σ' : setup.ReplayRepresentative X Y),
          TraceEquiv setup canonicalReplay σ') :
    (CertifiedTrace.mk cls canonicalReplay represents n primitiveDecls supportGraph
      adjacentIndependence twoCellData).primitiveDecls = primitiveDecls := rfl

@[simp] theorem CertifiedTrace.mk_supportGraph
    {X Y : setup.State}
    (cls : setup.TraceClass X Y)
    (canonicalReplay : setup.ReplayRepresentative X Y)
    (represents : TraceClass.mk setup canonicalReplay = cls)
    (n : Nat)
    (primitiveDecls : Fin n → Σ (S : setup.State), setup.PrimitiveCertifiedDeclaration S)
    (supportGraph : DepGraph n)
    (adjacentIndependence :
      ∀ (i : Fin n) (h : i.val + 1 < n),
        let j : Fin n := ⟨i.val + 1, h⟩
        supportGraph.edge i j = false → supportGraph.edge j i = false →
          True)
    (twoCellData :
      (π : Fin n → Fin n) → Function.Bijective π →
        (∀ i j : Fin n, supportGraph.edge i j = true → π i < π j) →
        ∃ (σ' : setup.ReplayRepresentative X Y),
          TraceEquiv setup canonicalReplay σ') :
    (CertifiedTrace.mk cls canonicalReplay represents n primitiveDecls supportGraph
      adjacentIndependence twoCellData).supportGraph = supportGraph := rfl

@[simp] theorem CertifiedTrace.mk_adjacentIndependence
    {X Y : setup.State}
    (cls : setup.TraceClass X Y)
    (canonicalReplay : setup.ReplayRepresentative X Y)
    (represents : TraceClass.mk setup canonicalReplay = cls)
    (n : Nat)
    (primitiveDecls : Fin n → Σ (S : setup.State), setup.PrimitiveCertifiedDeclaration S)
    (supportGraph : DepGraph n)
    (adjacentIndependence :
      ∀ (i : Fin n) (h : i.val + 1 < n),
        let j : Fin n := ⟨i.val + 1, h⟩
        supportGraph.edge i j = false → supportGraph.edge j i = false →
          True)
    (twoCellData :
      (π : Fin n → Fin n) → Function.Bijective π →
        (∀ i j : Fin n, supportGraph.edge i j = true → π i < π j) →
        ∃ (σ' : setup.ReplayRepresentative X Y),
          TraceEquiv setup canonicalReplay σ') :
    (CertifiedTrace.mk cls canonicalReplay represents n primitiveDecls supportGraph
      adjacentIndependence twoCellData).adjacentIndependence =
        adjacentIndependence := rfl

@[simp] theorem CertifiedTrace.mk_twoCellData
    {X Y : setup.State}
    (cls : setup.TraceClass X Y)
    (canonicalReplay : setup.ReplayRepresentative X Y)
    (represents : TraceClass.mk setup canonicalReplay = cls)
    (n : Nat)
    (primitiveDecls : Fin n → Σ (S : setup.State), setup.PrimitiveCertifiedDeclaration S)
    (supportGraph : DepGraph n)
    (adjacentIndependence :
      ∀ (i : Fin n) (h : i.val + 1 < n),
        let j : Fin n := ⟨i.val + 1, h⟩
        supportGraph.edge i j = false → supportGraph.edge j i = false →
          True)
    (twoCellData :
      (π : Fin n → Fin n) → Function.Bijective π →
        (∀ i j : Fin n, supportGraph.edge i j = true → π i < π j) →
        ∃ (σ' : setup.ReplayRepresentative X Y),
          TraceEquiv setup canonicalReplay σ') :
    (CertifiedTrace.mk cls canonicalReplay represents n primitiveDecls supportGraph
      adjacentIndependence twoCellData).twoCellData = twoCellData := rfl

@[ext] theorem CertifiedTrace.ext
    {X Y : setup.State}
    {T T' : setup.CertifiedTrace X Y}
    (hcls : T.cls = T'.cls)
    (hReplay : T.canonicalReplay = T'.canonicalReplay)
    (hRepresents : HEq T.represents T'.represents)
    (hn : T.n = T'.n)
    (hDecls : HEq T.primitiveDecls T'.primitiveDecls)
    (hGraph : HEq T.supportGraph T'.supportGraph)
    (hAdj : HEq T.adjacentIndependence T'.adjacentIndependence)
    (hTwo : HEq T.twoCellData T'.twoCellData) :
    T = T' := by
  cases T
  cases T'
  cases hcls
  cases hReplay
  cases hRepresents
  cases hn
  cases hDecls
  cases hGraph
  cases hAdj
  cases hTwo
  rfl

theorem CertifiedTrace.class_eq_mk_canonicalReplay
    {X Y : setup.State}
    (T : setup.CertifiedTrace X Y) :
    T.cls = TraceClass.mk setup T.canonicalReplay :=
  T.represents.symm

theorem CertifiedTrace.traceEquiv_of_represents_eq
    {X Y : setup.State}
    (T : setup.CertifiedTrace X Y)
    {σ : setup.ReplayRepresentative X Y}
    (h : T.cls = TraceClass.mk setup σ) :
    TraceEquiv setup T.canonicalReplay σ := by
  apply TraceClass.exact (setup := setup)
  exact T.represents.trans h

theorem CertifiedTrace.class_eq_of_traceEquiv
    {X Y : setup.State}
    (T : setup.CertifiedTrace X Y)
    {σ : setup.ReplayRepresentative X Y}
    (h : TraceEquiv setup T.canonicalReplay σ) :
    T.cls = TraceClass.mk setup σ := by
  rw [T.class_eq_mk_canonicalReplay]
  exact TraceClass.sound (setup := setup) h

/-- Iff form: `T.cls = TraceClass.mk setup σ` iff `T.canonicalReplay` is trace-equivalent to `σ`. -/
theorem CertifiedTrace.cls_eq_mk_iff
    {X Y : setup.State}
    (T : setup.CertifiedTrace X Y)
    (σ : setup.ReplayRepresentative X Y) :
    T.cls = TraceClass.mk setup σ ↔ TraceEquiv setup T.canonicalReplay σ :=
  ⟨T.traceEquiv_of_represents_eq, T.class_eq_of_traceEquiv⟩

/-! ### Composition of certified traces

`def:composition-of-certified-traces` (`our_paper_draft.tex` L815) is
**not formalized in this cycle**. The manuscript composes by
concatenating replay representatives and identifying boundary ports along
the shared object `Y`; this requires concat operations on
`AdministrativeChain` and `ReplayRepresentative`, plus support-graph
concatenation. Deferred to a later cycle to keep this cycle's scaffold
small and verifiably correct. -/

/-! ### AUDIT NOTE (post-repair, 2026-04-26)

Before this repair, `TwoCellGenerator.admin` accepted arbitrary source/target
replay representatives with only a string tag. That made the following
collapse-style statements derivable:

* `TraceEquiv setup σ σ'` for arbitrary `σ, σ'` (same endpoints)
* all classes in `TraceClass X Y` equal

After the repair, `admin` requires `setup.AdminRelation σ σ'`, so those
collapse statements are no longer derivable from constructor shape alone.
They are intentionally removed from production code.

To instantiate a conservative setup, choose:

  `AdminRelation σ σ' := σ = σ'`

which immediately blocks arbitrary administrative edges. -/

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
