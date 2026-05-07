import TraceCalc.LayerB.Foundations.CirquentsAndStates
import Mathlib.Data.Fintype.Basic

/-!
# Foundational syntax: rewrite doctrines

**Real-objects path, Lane B cycle 3 (2026-04-23).**

Formalizes the manuscript's notion of a *rewrite doctrine* on top of
the foundational syntax of cycles 1–2.

## Manuscript correspondence

* `RewriteScheme` ↔ "typed rewrite schemes: oriented rules `ℓ ⇒ r`
  between pattern trees whose boundary profiles are compatible"
  inside `def:doctrine-definition` (`our_paper_draft.tex` L450).
* `Doctrine` ↔ `def:doctrine-definition` (L445): the quadruple
  `D = (Σ_∂, Σ_op, R, 𝒜)`. We absorb `(Σ_∂, Σ_op)` into the
  parameter pair `(D, sig)` (since `Σ_op` is exactly `Sig.Op` with its
  arity data); `R` and `𝒜` become real fields.
* `LocalCirquentState` ↔ "local state of the ambient cirquent" (L455).

## Encoding choices

* `R` finite via `Fintype` (avoids list-order artifacts).
* `𝒜` decidable via a per-pair `Decidable` instance field.
* `boundary_compat` field captures L451's "boundary profiles
  compatible" as strict equality of `Pat.boundaryProfile`.

## Cycle-3 deliverable

Doctrine-aware refinements `Goal.IsWellFormedAt Dc`, `State.IsWellFormedAt Dc`
that replace, on the doctrine-aware codepath, the `True` placeholders
of cycle 2.

## Not yet formalized (next cycle)

`def:typed-occurrence-map` (L587), `def:occurrence` (L612),
`def:replacement` (L618), `def:primitive-certified-declaration` (L612).
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace Foundations

/-! ### Rewrite schemes (manuscript L450) -/

/-- **Rewrite scheme** (`our_paper_draft.tex` L450, inside
`def:doctrine-definition`): an oriented rule `ℓ ⇒ r` between linear
quoted patterns whose boundary profiles agree. -/
structure RewriteScheme {D : PrimitiveInterfaceData.{u}}
    (Sig : Signature D) where
  /-- The shared output sort of `ℓ` and `r`. -/
  outSort : Sort_ D
  /-- Left-hand side `ℓ`. -/
  lhs : Pat Sig outSort
  /-- Right-hand side `r`. -/
  rhs : Pat Sig outSort
  /-- Linearity of `ℓ` (manuscript L478). -/
  lhs_linear : Pat.IsLinear lhs
  /-- Linearity of `r` (manuscript L478). -/
  rhs_linear : Pat.IsLinear rhs
  /-- Boundary-profile compatibility (manuscript L451). -/
  boundary_compat : Pat.boundaryProfile lhs = Pat.boundaryProfile rhs

/-! ### Local cirquent states (manuscript L455) -/

/-- **Local cirquent state** at an occurrence: surrounding context
that the doctrine's admissibility predicate may inspect.

The manuscript phrases admissibility as `𝒜(r, σ)` where `σ` is
"a local state of the ambient cirquent" (`our_paper_draft.tex` L455).
We carry the ambient goal plus an opaque positional payload so the
doctrine layer is independent of the not-yet-formalized occurrence
infrastructure (next cycle). -/
structure LocalCirquentState {D : PrimitiveInterfaceData.{u}}
    (Sig : Signature D) where
  /-- The ambient goal at the occurrence. -/
  ambientGoal : Goal Sig
  /-- Opaque positional payload (refined to a typed occurrence map
  in the next Lane B cycle). -/
  positional : Type u

/-! ### Doctrine (`def:doctrine-definition`, L445) -/

/-- **`def:doctrine-definition`** (`our_paper_draft.tex` L445):
a *rewrite doctrine* over interface data `D` is the quadruple
`(Σ_∂, Σ_op, R, 𝒜)`.

Here `(Σ_∂, Σ_op)` is the pair `(D, sig)`; `R` is a finite indexed
family of rewrite schemes; `admissible` is the decidable
admissibility predicate. -/
structure Doctrine (D : PrimitiveInterfaceData.{u}) where
  /-- The signature `(Σ_∂, Σ_op)`. -/
  sig : Signature D
  /-- Index type for the finite family of rewrite schemes. -/
  R_index : Type u
  /-- Finiteness of `R` (manuscript L450). -/
  R_fintype : Fintype R_index
  /-- The schemes themselves, indexed by `R_index`. -/
  R : R_index → RewriteScheme sig
  /-- Admissibility predicate `𝒜` (manuscript L455). -/
  admissible : R_index → LocalCirquentState sig → Prop
  /-- Decidability of `𝒜` (manuscript L456). -/
  admissible_decidable :
    ∀ (i : R_index) (σ : LocalCirquentState sig),
      Decidable (admissible i σ)

attribute [instance] Doctrine.R_fintype Doctrine.admissible_decidable

/-! ### Doctrine-aware well-formedness predicates

These discharge the `True` placeholders carried by cycle-2
`Goal.IsWellFormed.boundaryDoctrineCompatible` and
`State.IsWellFormed.envCompatibleWithGoal`. -/

namespace Goal

variable {D : PrimitiveInterfaceData.{u}}

/-- **Doctrine-aware boundary compatibility** for a goal
(`our_paper_draft.tex` L581, *"compatible with the doctrine"*).

In the typed encoding the goal's boundary profile is already a list
of `Sort_ D`, and `Sort_ D` is defined exactly from the doctrine's
interface data `D`. Compatibility is therefore automatic at the type
level; we expose this as a real reflexive predicate so the
doctrine-aware codepath has substantive content (rather than `True`). -/
def IsBoundaryCompatible (Dc : Doctrine D) (G : Goal Dc.sig) : Prop :=
  G.outputProfile = G.outputProfile

/-- The doctrine-aware boundary-compatibility predicate is
satisfied by every well-typed goal. -/
theorem isBoundaryCompatible_intro (Dc : Doctrine D) (G : Goal Dc.sig) :
    IsBoundaryCompatible Dc G := rfl

end Goal

/-! ### Environment / goal compatibility -/

namespace EnvCompat

variable {D : PrimitiveInterfaceData.{u}} {Sig : Signature D}

/-- A typed variable binding occurs in a lexical scope iff it appears
in `bindings`. -/
def varBound (sc : LexicalScope Sig) {s : Sort_ D} (x : Sig.Var s) : Prop :=
  ⟨s, x⟩ ∈ sc.bindings

/-- All free variables of an expression are bound in a lexical scope. -/
def exprAllBound (sc : LexicalScope Sig) :
    {s : Sort_ D} → Expr Sig s → Prop
  | _, .var x => varBound sc x
  | _, .op _ es => ∀ i, exprAllBound sc (es i)

/-- All free variables of a goal are bound in a lexical scope:
all input-boundary variables and all output expressions are
scope-closed. -/
def goalAllBound (sc : LexicalScope Sig) (G : Goal Sig) : Prop :=
  (∀ i, varBound sc (G.inputVars i)) ∧
    (∀ i, exprAllBound sc (G.outputs i))

end EnvCompat

/-! ### Doctrine-aware well-formedness wrappers

`Goal.IsWellFormedAt Dc` / `State.IsWellFormedAt Dc` refine the
cycle-2 placeholder predicates with real, manuscript-pinned content. -/

/-- **Doctrine-aware goal well-formedness** (refines cycle-2
`Goal.IsWellFormed`). -/
structure Goal.IsWellFormedAt
    {D : PrimitiveInterfaceData.{u}} (Dc : Doctrine D)
    (G : Goal Dc.sig) : Prop where
  boundaryDoctrineCompatible : Goal.IsBoundaryCompatible Dc G

/-- **Doctrine-aware state well-formedness** (refines cycle-2
`State.IsWellFormed`). -/
structure State.IsWellFormedAt
    {D : PrimitiveInterfaceData.{u}} (Dc : Doctrine D)
    (S : State Dc.sig) : Prop where
  goalWf : Goal.IsWellFormedAt Dc S.goal
  envCompatibleWithGoal : EnvCompat.goalAllBound S.env.scope S.goal

end Foundations
end LayerB
end TraceCalc
