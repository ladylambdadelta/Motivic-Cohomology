import Mathlib.Data.List.Nodup

/-!
# Foundational syntax of the certified trace calculus

**Real-objects path, Lane B cycle 1 (2026-04-23).**

This file is the start of the *foundational* lane: it formalizes the
manuscript's primitive syntactic objects as **real inductive types**,
not opaque carriers. It is parallel to (and eventually intended to
instantiate) the opaque `RewriteCalculusSetup` of
`TraceCalc.LayerB.RealObjects.RewriteCalculus`.

## Manuscript correspondence

Every definition below cites the manuscript line in
`our_paper_draft.tex`:

* `PrimitiveInterfaceData` ↔ `def:primitive-interface-data` (L378).
  Manuscript: `Σ_∂ = (P_0, Π_pkt, C_int, σ, τ)`. We carry `P_0`,
  `Π_pkt`, `C_int`, and an arity `arityIn : C_int → ℕ` (used by the
  free algebra below); `σ`'s typed input profile is then absorbed into
  the inductive `Sort_` constructor `con`. `τ` (output profile) is not
  needed to build `Sort_`; we add it as a separate field as soon as a
  downstream definition consumes it.
* `Sort_ D` ↔ `def:intrinsic-sort-system` (L388).
  Manuscript: `S := Intf(Σ_∂)` defined inductively by clauses (i)–(iii).
  Our three constructors `port`, `gen`, `con` correspond exactly.
* `prop:free-interface-algebra` (L405) is a corollary of the inductive
  recursor; we record it explicitly via `Sort_.rec`-derived
  `Sort_.interp` and prove its uniqueness.
* `Signature Σ` carries `Var`, `Hole`, `Op` with arities — the data of
  `def:active-expressions` (L534) and the manuscript's variable/hole
  declarations (L473, L520).
* `Expr Sig s` ↔ `def:active-expressions` (L534): typed inductive
  active expressions of sort `s`.
* `Pat Sig s` ↔ `def:linear-quoted-patterns` (L477) without the
  linearity restriction; linearity is enforced separately via
  `Pat.holes` and `IsLinear`.
* `Pat.holes` enumerates, in source order, the list of (sort, hole)
  pairs occurring in a pattern. `IsLinear p` ↔ "each hole occurs at
  most once" (L477).
* `Pat.boundaryProfile` ↔ `def:boundary-profile` (L488): root-output
  sort followed by hole sorts in source order.
* `Pat.plug` ↔ `def:plugging` (L492): substitute expressions for
  holes.
* `theorem plug_total_and_sort_preserving` ↔ the proposition of L513.

## What this file does NOT yet contain

* `def:pattern-tree-and-core` (L484): the rooted-tree forgetful
  recipe. Adds nothing computational beyond what the inductive carries
  already; deferred.
* `def:quotation-and-quasiquotation` (L500): converts active
  expressions to patterns. Definable from `Expr` via a "lift to `Pat`"
  step; deferred to a separate cycle that will also formalize the
  expression-cirquent layer.
* Cirquents, goals, states, occurrences, replacement, primitive
  certified declarations: these are downstream and will land in
  subsequent Lane B cycles.

## Namespace

`TraceCalc.LayerB.Foundations`. Distinct from
`TraceCalc.LayerB.RealObjects` (the opaque-carrier vertical) and
from `TraceCalc.LayerB.ShadowModel` (the quarantined sandbox).
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace Foundations

/-! ### Primitive interface data and the intrinsic sort system -/

/-- **`def:primitive-interface-data`** (`our_paper_draft.tex` L378):
`Σ_∂ = (P_0, Π_pkt, C_int, σ, τ)`.

Here we carry `P_0` (primitive boundary-port labels), `Π_pkt`
(primitive packet-interface generators), `C_int` (structural interface
constructors), and the **input** arity of each constructor (`arityIn`).
The full input *profile* `σ(c) : Fin (arityIn c) → Sort_` is part of
the inductive `Sort_` constructor itself (see `Sort_.con`). `τ` (output
profile) is added later when a downstream definition consumes it. -/
structure PrimitiveInterfaceData where
  /-- `P_0`: primitive boundary-port labels (manuscript L380). -/
  P0 : Type u
  /-- `Π_pkt`: primitive packet-interface generators (manuscript L380). -/
  PiPkt : Type u
  /-- `C_int`: structural interface constructors (manuscript L380). -/
  CInt : Type u
  /-- For each constructor `c ∈ C_int`, the length of its input
  profile `σ(c)`. The actual typed profile is part of the inductive
  `Sort_.con` constructor below. -/
  arityIn : CInt → Nat

/-- **`def:intrinsic-sort-system`** (`our_paper_draft.tex` L388):
`S := Intf(Σ_∂)` is the least class generated inductively by
clauses (i)–(iii). The three constructors of `Sort_` correspond
exactly:

* `port p` ↔ clause (i): every primitive boundary-port label is an
  interface expression (L390).
* `gen π` ↔ clause (ii): every primitive packet-interface generator
  is an interface expression (L391).
* `con c args` ↔ clause (iii): if `c ∈ C_int` has input profile
  `(I_1, …, I_n)` with each `I_k` already an interface expression,
  then `c(I_1, …, I_n)` is an interface expression (L392). -/
inductive Sort_ (D : PrimitiveInterfaceData.{u}) : Type u
  | port : D.P0 → Sort_ D
  | gen : D.PiPkt → Sort_ D
  | con : (c : D.CInt) → (Fin (D.arityIn c) → Sort_ D) → Sort_ D

/-! ### Free interface algebra (manuscript `prop:free-interface-algebra`, L405)

The proposition states that `S` is the *free* interface algebra: any
assignment of the primitive data into a target algebra extends
uniquely to an interpretation `⟦-⟧ : S → A`. This is the universal
property of the inductive recursor. We expose it explicitly. -/

namespace Sort_

variable {D : PrimitiveInterfaceData.{u}}

/-- The interpretation `⟦-⟧ : S → A` extending an assignment of
primitive data. Existence half of `prop:free-interface-algebra`
(L405). -/
def interp {A : Type v}
    (fp : D.P0 → A) (fg : D.PiPkt → A)
    (fc : (c : D.CInt) → (Fin (D.arityIn c) → A) → A) :
    Sort_ D → A
  | port p => fp p
  | gen π => fg π
  | con c args => fc c (fun i => interp fp fg fc (args i))

/-- **`prop:free-interface-algebra`** (`our_paper_draft.tex` L405),
uniqueness half: any sort-preserving extension of the primitive
assignment agrees with `interp`. The proof is induction on `Sort_`. -/
theorem interp_unique {A : Type v}
    (fp : D.P0 → A) (fg : D.PiPkt → A)
    (fc : (c : D.CInt) → (Fin (D.arityIn c) → A) → A)
    (φ : Sort_ D → A)
    (hp : ∀ p, φ (port p) = fp p)
    (hg : ∀ π, φ (gen π) = fg π)
    (hc : ∀ (c : D.CInt) (args : Fin (D.arityIn c) → Sort_ D),
            φ (con c args) = fc c (fun i => φ (args i))) :
    ∀ s, φ s = interp fp fg fc s
  | port p => by simp [interp, hp]
  | gen π => by simp [interp, hg]
  | con c args => by
      rw [hc, interp]
      congr 1
      funext i
      exact interp_unique fp fg fc φ hp hg hc (args i)

end Sort_

/-! ### Signature: variables, holes, operation symbols -/

/-- Sortwise data of variables, holes, and operation symbols over a
fixed primitive interface signature. The variable family is
`def:variables-and-operation-symbols` (`our_paper_draft.tex` L520);
the hole family is `def:holes` (L473); the operation-symbol family is
also from L520 (input profile `ar(ω)` and output sort `coar(ω)`). -/
structure Signature (D : PrimitiveInterfaceData.{u}) where
  /-- `Var_s`: countable family of variables of each sort
  (manuscript L520). -/
  Var : Sort_ D → Type u
  /-- `Hole_s = □^s_i`: countable family of holes of each sort
  (manuscript `def:holes`, L473). -/
  Hole : Sort_ D → Type u
  /-- Operation symbols `ω` (manuscript L520). -/
  Op : Type u
  /-- Arity length of an operation symbol. -/
  opArity : Op → Nat
  /-- Typed input profile `ar(ω) = (s_1, …, s_m)` (L522). -/
  opIn : (ω : Op) → Fin (opArity ω) → Sort_ D
  /-- Output sort `coar(ω) = t` (L523). -/
  opOut : Op → Sort_ D

/-! ### Active expressions

`def:active-expressions` (`our_paper_draft.tex` L534): `Expr_s` is
generated inductively from variables of sort `s` and applied
operation symbols. -/

/-- **`def:active-expressions`** (`our_paper_draft.tex` L534): typed
active expressions over a signature `Sig`. The two constructors
correspond to the manuscript's "variables of sort `s`" and
"`ω(e_1, …, e_m)`" clauses. -/
inductive Expr {D : PrimitiveInterfaceData.{u}} (Sig : Signature D) :
    Sort_ D → Type u
  | var {s : Sort_ D} : Sig.Var s → Expr Sig s
  | op (ω : Sig.Op)
      (es : (i : Fin (Sig.opArity ω)) → Expr Sig (Sig.opIn ω i)) :
      Expr Sig (Sig.opOut ω)

/-! ### Linear quoted patterns

`def:linear-quoted-patterns` (`our_paper_draft.tex` L477): a *linear
quoted pattern* of sort `s` is an active expression of sort `s` built
from variables, operation symbols, and holes, with each hole occurring
at most once.

We model the underlying "quoted pattern" as an inductive `Pat`
allowing all three formers (variables, holes, applied operation
symbols), then enforce linearity via a separate `IsLinear` predicate
defined in terms of the hole-occurrence list `holes`. -/

/-- Quoted patterns of sort `s` over a signature: like `Expr`, plus a
`hole` constructor. Linearity (manuscript "each hole occurs at most
once") is a *separate* predicate `IsLinear` below, so the manuscript's
two constraints — typed syntactic shape and linearity — are
distinguished. -/
inductive Pat {D : PrimitiveInterfaceData.{u}} (Sig : Signature D) :
    Sort_ D → Type u
  | var {s : Sort_ D} : Sig.Var s → Pat Sig s
  | hole {s : Sort_ D} : Sig.Hole s → Pat Sig s
  | op (ω : Sig.Op)
      (ps : (i : Fin (Sig.opArity ω)) → Pat Sig (Sig.opIn ω i)) :
      Pat Sig (Sig.opOut ω)

namespace Pat

variable {D : PrimitiveInterfaceData.{u}} {Sig : Signature D}

/-- The list of (sort, hole) pairs occurring in a pattern, in source
order (left-to-right traversal). Used to enforce linearity (each hole
appears at most once) and to compute the boundary profile
(`def:boundary-profile`, L488). -/
def holes : {s : Sort_ D} → Pat Sig s → List (Σ' s : Sort_ D, Sig.Hole s)
  | _, .var _ => []
  | s, .hole h => [⟨s, h⟩]
  | _, .op ω ps =>
      (List.finRange (Sig.opArity ω)).flatMap (fun i => holes (ps i))

/-- **`def:linear-quoted-patterns`** (`our_paper_draft.tex` L477)
linearity clause: each hole occurs at most once. -/
def IsLinear {s : Sort_ D} (p : Pat Sig s) : Prop :=
  (holes p).Nodup

/-- The subtype of *linear* quoted patterns of sort `s`. This is
`Pat_s` of the manuscript (L478) under the strict reading. -/
def Linear (Sig : Signature D) (s : Sort_ D) : Type u :=
  { p : Pat Sig s // IsLinear p }

/-- **`def:boundary-profile`** (`our_paper_draft.tex` L488): the
ordered list of boundary ports of a pattern, consisting of the root
output sort together with the sorts of the ports occupied by holes,
in source order. -/
def boundaryProfile {s : Sort_ D} (p : Pat Sig s) : Sort_ D × List (Sort_ D) :=
  (s, (holes p).map (fun ⟨s', _⟩ => s'))

/-! ### Plugging (`def:plugging`, L492) -/

/-- **`def:plugging`** (`our_paper_draft.tex` L492): substitute
typed expressions for the holes of a pattern. Given a *total typed
filling* `θ s h : Expr Sig s` for every (sort, hole) pair, recursively
replace each hole `□^s_i` by `θ s i`.

Sort preservation is structural: the result has the same sort as the
input pattern. This is exactly the manuscript's `p[e_1, …, e_m]`
specialized to the global filling `θ`; the hole-indexed list version
of the manuscript reads off `holes p` and applies `θ` to its entries.

In our well-typed inductive encoding, the *typed* signature
`p : Pat Sig s → Expr Sig s` of `plug` is itself the manuscript's
"plug is total and sort-preserving" claim — see the theorem below. -/
def plug : {s : Sort_ D} → Pat Sig s →
    (θ : (s' : Sort_ D) → Sig.Hole s' → Expr Sig s') → Expr Sig s
  | _, .var x, _ => Expr.var x
  | _, .hole (s := s) h, θ => θ s h
  | _, .op ω ps, θ => Expr.op ω (fun i => plug (ps i) θ)

end Pat

/-! ### The first foundational theorem -/

/-- **`prop:plugging-is-total-and-sort-preserving`**
(`our_paper_draft.tex` L513): *"If `p ∈ Pat_s` and the inserted
expressions match the declared sorts of the holes of `p`, then
`p[e_1, …, e_m]` is a well-defined active expression of sort `s`."*

In the typed inductive encoding above, this is the *typing soundness*
of `Pat.plug`: for every linear pattern `p : Pat Sig s` and every
typed filling `θ`, the result `Pat.plug p θ` is a well-defined
expression of sort `s`. Both totality (no failure mode) and
sort-preservation (the output sort equals the input sort) are
captured by the dependent type signature itself, which is exactly
what the manuscript asserts.

The proof is therefore by reflexivity once the dependent type is
inhabited. We record the existential statement to make the manuscript
shape transparent. -/
theorem plug_total_and_sort_preserving
    {D : PrimitiveInterfaceData.{u}} {Sig : Signature D}
    {s : Sort_ D} (p : Pat Sig s)
    (θ : (s' : Sort_ D) → Sig.Hole s' → Expr Sig s') :
    ∃ e : Expr Sig s, Pat.plug p θ = e :=
  ⟨Pat.plug p θ, rfl⟩

end Foundations
end LayerB
end TraceCalc
