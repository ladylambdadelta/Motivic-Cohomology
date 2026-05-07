import TraceCalc.LayerB.Foundations.Syntax

/-!
# Foundational syntax: quotation, cirquents, goals, states

**Real-objects path, Lane B cycle 2 (2026-04-23).**

This file extends `TraceCalc.LayerB.Foundations.Syntax` (Lane B
cycle 1) with the next layer of the manuscript's primitive ontology:

* `Pat.quote` ↔ `def:quotation-and-quasiquotation` quotation half
  (`our_paper_draft.tex` L500).
* `Pat.quasiQuote` ↔ same definition, quasiquotation half (L502).
* `quote_holes_empty`, `quote_isLinear` — basic equational lemmas.
* `ExprCirquent` ↔ `def:expression-cirquent` (L553).
* `BoundaryCirquent` ↔ `def:boundary-cirquent-and-goal` (L557).
* `Goal` ↔ same definition, goal half.
* `Expr.toCanonicalCirquent` ↔
  `def:canonical-cirquent-of-an-active-expression` (L573).
* `LexicalScope`, `DefinitionEnvironment` ↔
  `def:lexical-scope-and-definition-environment` (L577).
* `State` ↔ `def:state` (L565).
* `Goal.IsWellFormed`, `State.IsWellFormed` ↔
  `def:well-formed-goal-and-well-formed-state` (L581).

## Encoding choices and honest scope

* The manuscript's expression cirquent is "a finite directed acyclic
  hypergraph whose nodes are labelled by sorts and operation symbols"
  (L553). The manuscript also notes (L573) that *"shared subexpressions
  may be identified when the surrounding context requires a common
  resource"* — i.e., sharing is **optional**, not forced. We adopt the
  unfolded-tree encoding: an `ExprCirquent` is a typed list of `Expr`s,
  one per output port. Sort-typing and finiteness are dependent-type
  invariants. Acyclicity is automatic because `Expr` is an inductive
  tree. Optional sharing identification is a downstream optimization
  that does not change the type and is not required by any later
  manuscript object until the support graph is computed (deferred).
  This is a faithful but **strict-tree** reading of L553; we flag it
  honestly in `ExprCirquent`'s docstring.

* `def:boundary-cirquent-and-goal` (L557) makes boundary cirquent and
  goal essentially synonymous: a goal `(C, ∂C)` *is* a cirquent with
  its ordered boundary annotation. We model both with one structure
  `BoundaryCirquent` and define `Goal := BoundaryCirquent`, exactly as
  the manuscript pair indicates.

* `def:state` (L565): `S = (E, G)`. The definition environment `E` is
  described informally at L577 ("a finite record of scope data
  together with the local declarations needed to interpret the current
  goal and its admissible rewrites"). We model `LexicalScope` as a
  list of typed variable bindings and `DefinitionEnvironment` as a
  bundle of scope + an opaque `localDeclarations : Type u` field.
  **Manuscript-clarity flag**: the precise content of "local
  declarations" (e.g., let-bindings, doctrine-specific axioms) is not
  fixed at this point in the manuscript; we carry it as an opaque
  parameter of the cycle so that the encoding is honest about its
  open-endedness without committing to a specific concrete form yet.

* `def:well-formed-goal-and-well-formed-state` (L581): "well formed if
  its cirquent is finite, acyclic, and correctly sorted, and if its
  ordered boundary ports are compatible with the doctrine". Finiteness
  + acyclicity + correct sorting are dependent-type invariants here
  (an inductive `Expr` is automatically a finite acyclic well-sorted
  tree). The "compatible with the doctrine" clause refers forward to a
  doctrine that has not yet been formalized in Lane B; we expose it as
  a separate `Prop` slot `Goal.boundaryDoctrineCompatible` carrying a
  `True` placeholder, and **document that this is the only
  doctrine-dependent condition that must be discharged later**.

* `LexicalScope.IsCompatible` similarly carries the L582 condition
  *"definition environment is compatible with its current goal"* as a
  clearly-named placeholder until lexical-scope checking can be
  pinned down by a concrete doctrine.

## What this file does NOT contain

* `def:typed-occurrence-map` (L587), `def:occurrence` (L599),
  `def:replacement` (L607), `def:primitive-certified-declaration`
  (L611) on real syntax. These are the next Lane B cycle.
* The bridge instantiating the opaque `RewriteCalculusSetup` (Lane A)
  from these real foundations.
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace Foundations

variable {D : PrimitiveInterfaceData.{u}} {Sig : Signature D}

/-! ### Quotation and quasiquotation (`def:quotation-and-quasiquotation`, L500) -/

namespace Pat

/-- **`def:quotation-and-quasiquotation`**, quotation half
(`our_paper_draft.tex` L500): *"Quotation sends an active expression
to the corresponding hole-free pattern."*

Recursively map `Expr.var x ↦ Pat.var x` and `Expr.op ω es ↦
Pat.op ω (es ↦ quote)`. -/
def quote : {s : Sort_ D} → Expr Sig s → Pat Sig s
  | _, .var x => .var x
  | _, .op ω es => .op ω (fun i => quote (es i))

/-- A *quasiquotation selector*: a partial typed assignment mapping
sub-expressions to holes. `def:quotation-and-quasiquotation`
quasiquotation half (`our_paper_draft.tex` L502): *"Quasiquotation
allows selected subexpressions to be replaced by holes."*

A `Selector` says, at any subterm `e : Expr Sig s`, whether to
replace `e` by a hole `h : Sig.Hole s` (returning `some h`) or to
recurse structurally (returning `none`). -/
def Selector (Sig : Signature D) : Type u :=
  (s : Sort_ D) → Expr Sig s → Option (Sig.Hole s)

/-- **`def:quotation-and-quasiquotation`**, quasiquotation half
(`our_paper_draft.tex` L502): replace selected subterms by holes,
recursing structurally elsewhere. -/
def quasiQuote (sel : Selector Sig) :
    {s : Sort_ D} → Expr Sig s → Pat Sig s
  | _, e =>
    match sel _ e with
    | some h => .hole h
    | none =>
      match e with
      | .var x => .var x
      | .op ω es => .op ω (fun i => quasiQuote sel (es i))

/-- The empty selector — equivalent to `quote`. -/
def emptySelector (Sig : Signature D) : Selector Sig :=
  fun _ _ => none

/-! #### Equational lemmas about `quote` -/

/-- Quotation produces no holes. -/
theorem quote_holes_empty : ∀ {s : Sort_ D} (e : Expr Sig s),
    (quote e).holes = []
  | _, .var _ => rfl
  | _, .op ω es => by
      show (List.finRange (Sig.opArity ω)).flatMap
        (fun i => (quote (es i)).holes) = []
      have ih : ∀ i, (quote (es i)).holes = [] :=
        fun i => quote_holes_empty (es i)
      induction List.finRange (Sig.opArity ω) with
      | nil => rfl
      | cons a as ihL => simp [List.flatMap_cons, ih a, ihL]

/-- Quotation produces a linear pattern (no hole appears more than
once — vacuously, since there are no holes). -/
theorem quote_isLinear {s : Sort_ D} (e : Expr Sig s) :
    IsLinear (quote e) := by
  unfold IsLinear
  rw [quote_holes_empty]
  exact List.nodup_nil

end Pat

/-! ### Expression cirquents (`def:expression-cirquent`, L553) -/

/-- **`def:expression-cirquent`** (`our_paper_draft.tex` L553): a
finite DAG with sort-and-operation-labelled nodes and predecessor
slots matching declared input profiles.

Encoding choice (see file docstring): we adopt the strict-tree
reading. An `ExprCirquent Sig` is a typed tuple of active
expressions, one per output port. Finiteness, acyclicity, and correct
sorting are dependent-type invariants of the inductive `Expr`.
Optional shared-subexpression identification (L573) is not required
by any object formalized here and is deferred. -/
structure ExprCirquent (Sig : Signature D) where
  /-- Sort profile of the cirquent's output ports. -/
  outputProfile : List (Sort_ D)
  /-- The active expression at each output port, typed by its sort. -/
  outputs : (i : Fin outputProfile.length) →
    Expr Sig (outputProfile.get i)

/-! ### Boundary cirquents and goals (`def:boundary-cirquent-and-goal`, L557) -/

/-- **`def:boundary-cirquent-and-goal`** (`our_paper_draft.tex` L557):
a boundary cirquent is a finite cirquent equipped with an ordered
tuple of designated boundary ports. The pair `(C, ∂C)` of a goal is
exactly this data.

We carry the **input-boundary** profile too (manuscript: *"the
external interface through which traces compose"*, L559). Inputs
appear inside `outputs` as free variables typed by `inputProfile`. -/
structure BoundaryCirquent (Sig : Signature D) where
  /-- Sort profile of the input boundary `∂_in C`. -/
  inputProfile : List (Sort_ D)
  /-- Sort profile of the output boundary `∂_out C`. -/
  outputProfile : List (Sort_ D)
  /-- The variable name attached to each input boundary port. The
  manuscript's "external interface" is read by treating these
  variables as the entry points through which composition slotwise
  identifies target ports of the prior trace with source ports of
  this one (`def:boundary-object`, L414). -/
  inputVars : (i : Fin inputProfile.length) →
    Sig.Var (inputProfile.get i)
  /-- The active expression at each output port. -/
  outputs : (i : Fin outputProfile.length) →
    Expr Sig (outputProfile.get i)

/-- **`def:boundary-cirquent-and-goal`** (`our_paper_draft.tex` L559),
goal half: *"a goal is a pair `G = (C, ∂C)` of an expression cirquent
together with its ordered boundary."*

In our encoding `BoundaryCirquent` already carries both the cirquent
and its ordered boundary, so `Goal` is a synonym. -/
abbrev Goal (Sig : Signature D) : Type u := BoundaryCirquent Sig

/-! ### Canonical cirquent of an active expression
(`def:canonical-cirquent-of-an-active-expression`, L573) -/

namespace Expr

/-- **`def:canonical-cirquent-of-an-active-expression`**
(`our_paper_draft.tex` L573): every active expression `e` of sort `s`
determines a single-output expression cirquent `C_e`. -/
def toCanonicalCirquent {s : Sort_ D} (e : Expr Sig s) : ExprCirquent Sig where
  outputProfile := [s]
  outputs := fun ⟨0, _⟩ => e

end Expr

/-! ### Lexical scope, definition environment, state
(`def:lexical-scope-and-definition-environment`, L577;
`def:state`, L565) -/

/-- **`def:lexical-scope-and-definition-environment`**
(`our_paper_draft.tex` L577): a *lexical scope* specifies which
variables (and operation symbols) are available at a given stage of
a trace. We model it as a finite list of typed variable bindings;
the operation-symbol part of the scope is fully shared with the
ambient `Sig.Op` and needs no per-state restriction in this cycle. -/
structure LexicalScope (Sig : Signature D) where
  /-- Finite list of currently-available typed variable bindings. -/
  bindings : List (Σ' s : Sort_ D, Sig.Var s)

/-- **`def:lexical-scope-and-definition-environment`**
(`our_paper_draft.tex` L577): a *definition environment* is a finite
record of scope data together with local declarations needed to
interpret the current goal and its admissible rewrites.

**Manuscript-clarity flag (carried honestly):** the precise content
of "local declarations" is not fixed at this point in the manuscript
(e.g., let-bindings, doctrine axioms). We carry it as an opaque
`localDeclarations : Type u` field so the encoding is honest about
the open-endedness without committing to a specific form. -/
structure DefinitionEnvironment (Sig : Signature D) where
  /-- Lexical scope of currently-available bindings. -/
  scope : LexicalScope Sig
  /-- Opaque per-environment local declarations (placeholder pending
  doctrine-specific concrete content; see this file's docstring). -/
  localDeclarations : Type u

/-- **`def:state`** (`our_paper_draft.tex` L565): a state is a pair
`S = (E, G)` of a definition environment and a well-formed goal. -/
structure State (Sig : Signature D) where
  /-- Definition environment `E`. -/
  env : DefinitionEnvironment Sig
  /-- Current goal `G`. -/
  goal : Goal Sig

/-! ### Well-formedness (`def:well-formed-goal-and-well-formed-state`, L581) -/

/-- **`def:well-formed-goal-and-well-formed-state`**
(`our_paper_draft.tex` L581), goal half: *"a goal is well formed if
its cirquent is finite, acyclic, and correctly sorted, and if its
ordered boundary ports are compatible with the doctrine."*

In our encoding, finiteness + acyclicity + correct sorting are
**already dependent-type invariants** of `BoundaryCirquent` and
`Expr`. The remaining condition — boundary-port compatibility with
the doctrine — refers forward to a doctrine that has not yet been
formalized in Lane B; we expose it as a separate `Prop` slot
carrying a `True` placeholder. -/
structure Goal.IsWellFormed (G : Goal Sig) : Prop where
  /-- Boundary-port compatibility with the doctrine. Placeholder
  pending Lane B doctrine formalization. -/
  boundaryDoctrineCompatible : True

/-- **`def:well-formed-goal-and-well-formed-state`**
(`our_paper_draft.tex` L582), state half: *"a state is well formed
if its definition environment is compatible with its current goal."*

Carried as a clearly-named placeholder predicate together with the
goal-well-formedness witness. -/
structure State.IsWellFormed (S : State Sig) : Prop where
  /-- The state's goal is well-formed. -/
  goalWf : S.goal.IsWellFormed
  /-- Definition-environment / goal compatibility. Placeholder
  pending Lane B doctrine formalization. -/
  envCompatibleWithGoal : True

end Foundations
end LayerB
end TraceCalc
