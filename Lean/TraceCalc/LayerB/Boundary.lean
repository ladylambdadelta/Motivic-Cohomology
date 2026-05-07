import Mathlib.Data.List.FinRange

/-!
# Canonical syntactic boundary assignment (Layer B)

This file formalizes the load-bearing combinatorial content of

  Theorem (Canonical syntactic fiber assignment), `thm:canonical-syntactic-fiber-assignment`,
  manuscript line ~4432.

The manuscript proof builds, by recursion on the free interface algebra
`S = Intf(Σ_∂)` (Definition L388, Proposition `prop:free-interface-algebra` L406),
a finite ordered set `∂s` of typed boundary slots, then sets the canonical syntactic
fibers to `Q⟨∂s⟩` with comparison map equal to the identity on the common basis.

Scope (from `TEX_TO_LEAN_MAP.md`, classification CLT, layer L1):
the file captures the combinatorial datum `s ↦ ∂s` and its constructor recurrence.
The `Q`-linear fiber assignment is a downstream wrapper and is intentionally
not introduced here, to avoid widening the imports beyond what this theorem
actually needs.

Authorization to open this file: §"Refinements authorized by this map" item 5,
triggered by the row `thm:canonical-syntactic-fiber-assignment`.

Source-of-truth note: the names `Prim`, `Constr`, `arity`, `primSlots` here
correspond, respectively, to the manuscript's `P₀ ⊔ Π_pkt`, `C_int`, the
arity portion of `(σ, τ)`, and the declared finite ordered interface attached
to each primitive. We collapse `P₀` and `Π_pkt` into a single `Prim` because
the canonical syntactic boundary treats them uniformly (both contribute their
declared finite ordered interface). The bound name `sig` stands in for the
manuscript's `Σ_∂`; the symbol `Σ` itself is reserved Lean syntax.
-/

universe u

namespace TraceCalc
namespace LayerB

/-- Primitive interface data `Σ_∂ = (P₀, Π_pkt, C_int, σ, τ)` from the manuscript
(Definition at L380), packaged for the canonical syntactic boundary construction.

`Slot` is the ambient type of typed boundary slots.

For each structural interface constructor `c : Constr`, `arity c` is the number of
input interface arguments; the manuscript's `σ` is captured implicitly by the fact
that constructors take a tuple of `Sort_` values, and the manuscript's `τ` (the output
profile) is determined automatically by the canonical boundary recurrence below — there
is no extra slot data attached to a constructor in the canonical syntactic case. -/
structure BoundarySignature (Slot : Type u) where
  /-- `P₀ ⊔ Π_pkt`: primitive boundary-port labels and primitive packet-interface generators. -/
  Prim : Type u
  /-- `C_int`: structural interface constructors. -/
  Constr : Type u
  /-- Number of input-interface arguments of each constructor. -/
  arity : Constr → Nat
  /-- Declared finite ordered interface attached to each primitive. -/
  primSlots : Prim → List Slot

/-- The intrinsic sort system `S = Intf(Σ_∂)`, i.e. the free interface algebra on
`Σ_∂` (Definition at L388, characterized by Proposition `prop:free-interface-algebra` L406). -/
inductive Sort_ {Slot : Type u} (sig : BoundarySignature Slot) : Type u
  | prim   : sig.Prim → Sort_ sig
  | constr : (c : sig.Constr) → (Fin (sig.arity c) → Sort_ sig) → Sort_ sig

namespace Sort_

variable {Slot : Type u} {sig : BoundarySignature Slot}

/-- The canonical boundary assignment `∂ : S → List Slot`.

This is the recursion in the proof of `thm:canonical-syntactic-fiber-assignment`
(manuscript L4451): a primitive sort gets its declared interface, and a constructor
sort gets the disjoint union, in declared order, of the boundaries of its inputs. -/
def boundary : Sort_ sig → List Slot
  | .prim p        => sig.primSlots p
  | .constr c args =>
      (List.finRange (sig.arity c)).flatMap (fun i => boundary (args i))

@[simp] theorem boundary_prim (p : sig.Prim) :
    boundary (Sort_.prim (sig := sig) p) = sig.primSlots p := rfl

/-- Constructor recurrence for the canonical boundary assignment. This is the
content of clause (iii) of the proof at L4451. -/
@[simp] theorem boundary_constr
    (c : sig.Constr) (args : Fin (sig.arity c) → Sort_ sig) :
    boundary (Sort_.constr c args)
      = (List.finRange (sig.arity c)).flatMap (fun i => boundary (args i)) := rfl

/-- The canonical syntactic fiber dimension `dim_Q ω^syn(s) = #∂s`.

The manuscript identifies the Betti and de Rham syntactic fibers with
`Q⟨∂s⟩` (theorem statement at L4432); this function records their common
finite dimension without committing to a specific algebraic encoding. -/
def fiberDim (s : Sort_ sig) : Nat := (boundary s).length

@[simp] theorem fiberDim_prim (p : sig.Prim) :
    fiberDim (Sort_.prim (sig := sig) p) = (sig.primSlots p).length := rfl

end Sort_

end LayerB
end TraceCalc
