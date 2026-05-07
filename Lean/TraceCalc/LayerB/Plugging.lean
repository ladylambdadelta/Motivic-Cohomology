import TraceCalc.LayerB.Boundary

/-!
# Plugging shadow model (Layer B, sandbox)

**STATUS (reclassified 2026-04-23, per the new strict standard):**
**SHADOW MODEL / SANDBOX. THIS FILE DOES NOT FORMALIZE THE MANUSCRIPT PROPOSITION.**

Everything in this file lives in namespace `TraceCalc.LayerB.ShadowModel`.
The `apply_comp` theorem proved here is `List.flatMap` associativity in a
normalized substrate where:

* closed realizations are `List (Fin (Sort_.fiberDim t))` rather than
  elements of the manuscript's `Q⟨∂t⟩`;
* routings are bare functions on slot indices rather than typed Q-multilinear
  incidence maps with quasi-quotation;
* only the single-hole (`m = 1`) case is modeled.

As such this file is **not** a formalization of `prop:syntactic-plugging-law`
(`our_paper_draft.tex` L4471). Per `TEX_TO_LEAN_MAP.md` §"Anti-impersonation
rule (strict standard)", the corresponding map row has been demoted to record
"no formalization yet".

## Original (pre-reclassification) introduction

The file was originally introduced as the load-bearing combinatorial slice of

  Proposition (Syntactic plugging law), `prop:syntactic-plugging-law`,
  manuscript line ~4471.

Manuscript context (lines 4461–4485):

* `def:syntactic-open-context-realization` (L4461) defines the canonical syntactic
  realization of an open context `p ∈ Pat_t` with hole sorts `s_1,…,s_m` as the
  Q-multilinear incidence map determined by the typed boundary-slot routing of `p`:
  on a basis tensor `e_{α_1} ⊗ ⋯ ⊗ e_{α_m}`, the image is the formal sum of those
  `e_β` (β ∈ ∂t) reached via the canonical cirquent of `p`.

* `prop:syntactic-plugging-law` (L4471) asserts that for closed expressions
  `e_k ∈ Expr_{s_k}`,
  `R^syn(p[e_1,…,e_m]) = R^syn(p)(R^syn(e_1), …, R^syn(e_m))`.

* The manuscript proof: "Both sides compute the same composite incidence relation
  on boundary slots…composition of typed slot-routing relations."

Scope (read this before extending):

* We model closed realizations at output sort `t` by `List (Fin (Sort_.fiberDim t))`,
  i.e. by formal sums of basis vectors with N-coefficients via the multiset structure
  of `List`. Q-coefficients are not needed for the plugging law as stated, since the
  manuscript's definition produces only `0/1` coefficients ("the sum of those output
  basis vectors" — multiplicity-free); using `List` proves a slightly stronger
  order-sensitive equation that immediately implies the multiset/Q-vector-space form.

* We prove the *single-hole* case (`m = 1`) of the plugging law in full. This is the
  algebraic core: it reduces, in our representation, to associativity of `flatMap`
  (`>=>` for the list monad). The general `m`-hole case is the iterated single-hole
  version; a faithful formalization of the full pattern-tree machinery is deferred
  along with `thm:canonical-reconstruction-algorithm`, per the authorization list
  in `TEX_TO_LEAN_MAP.md`.

* No Q-vector-space structure, no `Mathlib.Algebra.Module`, no `Mathlib.LinearAlgebra`.
  Those would be required to state and prove the *multilinear* version on
  `Module.Free Q (Fin n)`, which is downstream of the combinatorial routing equation
  proved here.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace ShadowModel

open TraceCalc.LayerB

variable {Slot : Type u} {sig : BoundarySignature Slot}

/-- A *closed realization* at output sort `t` is a formal sum of boundary-slot basis
vectors with N-coefficients. We represent it concretely as a list over
`Fin (fiberDim t)`, so that an element with multiplicity `n` appears `n` times.

Manuscript correspondence: this is `R^syn(e) ∈ ω^syn(t) = Q⟨∂t⟩` (L4432),
restricted to the `0/1`-coefficient image of the canonical syntactic realization. -/
abbrev ClosedRealization (t : Sort_ sig) : Type :=
  List (Fin (Sort_.fiberDim t))

/-- A *single-hole open routing* from sort `s` (the hole) to output sort `t` is the
typed boundary-slot routing of `def:syntactic-open-context-realization` in the
`m = 1` case: for each input boundary slot `α ∈ ∂s`, the list of output boundary
slots `β ∈ ∂t` reached by the pattern's canonical cirquent. -/
def Routing₁ (s t : Sort_ sig) : Type :=
  Fin (Sort_.fiberDim s) → List (Fin (Sort_.fiberDim t))

namespace Routing₁

variable {s t u : Sort_ sig}

/-- Multilinear application of a single-hole routing on a closed filler.

This is the `m = 1` case of the open-context realization
(`def:syntactic-open-context-realization`, L4461): on the formal-sum filler
`Σ_{α ∈ filler} e_α`, the routing produces `Σ_{α ∈ filler} R(α)`,
which we represent by `filler.flatMap R`. -/
def apply (R : Routing₁ s t) (filler : ClosedRealization s) : ClosedRealization t :=
  filler.flatMap R

/-- Vertical composition of single-hole routings: routing `R₂ : t → u` after
routing `R₁ : s → t`. Manuscript correspondence: this is the slot-level
composition of typed routing relations referenced in the proof of
`prop:syntactic-plugging-law` ("composition of typed slot-routing relations"). -/
def comp (R₂ : Routing₁ t u) (R₁ : Routing₁ s t) : Routing₁ s u :=
  fun α => (R₁ α).flatMap R₂

/-- The syntactic plugging law, single-hole case (`m = 1` of
`prop:syntactic-plugging-law`).

Realizing the substituted closed expression equals first realizing the filler and
then applying the outer routing. In our model both reduce to `List.flatMap`
associativity.

This is the algebraic core that any genuine pattern-syntax formulation reduces to:
"Both sides compute the same composite incidence relation on boundary slots."
(manuscript proof of `prop:syntactic-plugging-law`). -/
theorem apply_comp
    (R₂ : Routing₁ t u) (R₁ : Routing₁ s t) (filler : ClosedRealization s) :
    (R₂.comp R₁).apply filler = R₂.apply (R₁.apply filler) := by
  unfold apply comp
  exact (List.flatMap_assoc filler R₁ R₂).symm

end Routing₁

end ShadowModel
end LayerB
end TraceCalc
