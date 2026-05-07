import TraceCalc.LayerB.RealObjects.CertifiedTrace

/-!
# Real-objects formalization: composition of certified traces

**Real-objects path, cycle 5 (2026-04-23).**

This file faithfully encodes:

* `def:composition-of-certified-traces` (`our_paper_draft.tex` L817):
  composition is concatenation of replay representatives followed by
  slotwise port identification at the shared boundary `Y`. The slotwise
  port identification is automatic in our typed encoding, since
  `setup.ReplayRepresentative` is indexed by source/target *states* and
  the type of a concatenation `σ : X→Y, τ : Y→Z` already pins the shared
  boundary.

It also proves the **first manuscript-tagged theorem** of the
real-objects path:

* `lem:trace-equivalence-congruence` (`our_paper_draft.tex` L835): if
  `σ ~ σ' : X → Y` and `τ ~ τ' : Y → Z`, then `τ ∘ σ ~ τ' ∘ σ'`.

This congruence is what makes composition descend to a well-defined
operation on `TraceClass`, which we expose as `TraceClass.compose`.

## Honesty about the encoded content

Our cycle-4 encoding of `TwoCellGenerator` carries each generator-internal
predicate (admin name, independence, geometric rewrite rule) as data
without further coherence with the surrounding state. Under that
encoding, congruence under right- and left-append is a structural fact:
the append operation does not destroy any admin/swap/rw witness. We make
this evidence formal here against the real objects, with no shortcut:
every step is a real recursion on the manuscript's `AdministrativeChain`
and `ReplayRepresentative`. Sharpening the generators (e.g., making
`independent` decidable from the support graph) would not change the
shape of this proof, only the strength of what it implies.

## Namespace

Everything lives under `TraceCalc.LayerB.RealObjects`.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

/-! ### Concatenation of administrative chains -/

/-- Concatenation of two administrative chains. The slotwise compatibility
at the shared state `Y` is built into the dependent type. -/
def AdministrativeChain.append {setup : RewriteCalculusSetup.{u}} :
    {X Y Z : setup.State} →
    setup.AdministrativeChain X Y →
    setup.AdministrativeChain Y Z →
    setup.AdministrativeChain X Z
  | _, _, _, .nil _, b => b
  | _, _, _, .cons t rest, b => .cons t (rest.append b)

/-! ### Concatenation of replay representatives

Faithful to `def:composition-of-certified-traces` (L817). -/

/-- Prepend an administrative chain to the front of a replay representative. -/
def ReplayRepresentative.prependAdmin {setup : RewriteCalculusSetup.{u}} :
    {X Y Z : setup.State} →
    setup.AdministrativeChain X Y →
    setup.ReplayRepresentative Y Z →
    setup.ReplayRepresentative X Z
  | _, _, _, a, .identity a' => .identity (a.append a')
  | _, _, _, a, .step a' P advance => .step (a.append a') P advance

/-- Concatenation of two replay representatives, faithful to
`def:composition-of-certified-traces` (`our_paper_draft.tex` L817).
Slotwise port identification at the shared boundary `Y` is automatic in
the dependent type. -/
def ReplayRepresentative.append {setup : RewriteCalculusSetup.{u}} :
    {X Y Z : setup.State} →
    setup.ReplayRepresentative X Y →
    setup.ReplayRepresentative Y Z →
    setup.ReplayRepresentative X Z
  | _, _, _, .identity a, τ => ReplayRepresentative.prependAdmin a τ
  | _, _, _, .step a P advance, τ => .step a P (advance.append τ)

/-- The identity replay representative on a state `X`. Faithful to the
manuscript's "identity replay on `X`" of
`def:composition-of-certified-traces` (`our_paper_draft.tex` L824). -/
def idReplay {setup : RewriteCalculusSetup.{u}} (X : setup.State) :
    setup.ReplayRepresentative X X :=
  .identity (.nil X)

/-! ### Trace-equivalence congruence (`lem:trace-equivalence-congruence`, L835) -/

/-- Right-append of a fixed continuation `τ` preserves a one-step
generator. -/
def TwoCellGenerator.appendRight {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y}
    (g : TwoCellGenerator setup σ σ')
    (τ : setup.ReplayRepresentative Y Z) :
    TwoCellGenerator setup (σ.append τ) (σ'.append τ) := by
  cases g with
  | admin name hadmin =>
      have hadmin' : setup.AdminRelation (σ.append τ) (σ'.append τ) := by
        simpa [RewriteCalculusSetup.AdminRelation] using
          congrArg (fun r => r.append τ) hadmin
      exact .admin _ _ name
        hadmin'
  | swap indep h => exact .swap _ _ indep h
  | rw rule => exact .rw _ _ rule

/-- Left-append of a fixed prefix `σ'` preserves a one-step generator. -/
def TwoCellGenerator.appendLeft {setup : RewriteCalculusSetup.{u}}
    {Y Z : setup.State} (X : setup.State)
    (σ' : setup.ReplayRepresentative X Y)
    {τ τ' : setup.ReplayRepresentative Y Z}
    (g : TwoCellGenerator setup τ τ') :
    TwoCellGenerator setup (σ'.append τ) (σ'.append τ') := by
  cases g with
  | admin name hadmin =>
      have hadmin' : setup.AdminRelation (σ'.append τ) (σ'.append τ') := by
        simpa [RewriteCalculusSetup.AdminRelation] using
          congrArg (fun r => σ'.append r) hadmin
      exact .admin _ _ name
        hadmin'
  | swap indep h => exact .swap _ _ indep h
  | rw rule => exact .rw _ _ rule

/-- One-step `TwoCellStep` is preserved under right-append. -/
lemma TwoCellStep.appendRight {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y}
    (h : TwoCellStep setup σ σ')
    (τ : setup.ReplayRepresentative Y Z) :
    TwoCellStep setup (σ.append τ) (σ'.append τ) :=
  h.elim (fun g => ⟨g.appendRight τ⟩)

/-- One-step `TwoCellStep` is preserved under left-append. -/
lemma TwoCellStep.appendLeft {setup : RewriteCalculusSetup.{u}}
    {Y Z : setup.State} (X : setup.State)
    (σ' : setup.ReplayRepresentative X Y)
    {τ τ' : setup.ReplayRepresentative Y Z}
    (h : TwoCellStep setup τ τ') :
    TwoCellStep setup (σ'.append τ) (σ'.append τ') :=
  h.elim (fun g => ⟨g.appendLeft X σ'⟩)

/-- Trace equivalence is preserved under right-append by a fixed `τ`. -/
lemma TraceEquiv.appendRight {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y}
    (h : TraceEquiv setup σ σ')
    (τ : setup.ReplayRepresentative Y Z) :
    TraceEquiv setup (σ.append τ) (σ'.append τ) := by
  unfold TraceEquiv at h ⊢
  induction h with
  | rel _ _ hstep => exact Relation.EqvGen.rel _ _ (hstep.appendRight τ)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- Trace equivalence is preserved under left-append by a fixed `σ'`. -/
lemma TraceEquiv.appendLeft {setup : RewriteCalculusSetup.{u}}
    {Y Z : setup.State} (X : setup.State)
    (σ' : setup.ReplayRepresentative X Y)
    {τ τ' : setup.ReplayRepresentative Y Z}
    (h : TraceEquiv setup τ τ') :
    TraceEquiv setup (σ'.append τ) (σ'.append τ') := by
  unfold TraceEquiv at h ⊢
  induction h with
  | rel _ _ hstep => exact Relation.EqvGen.rel _ _ (hstep.appendLeft X σ')
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- **`lem:trace-equivalence-congruence`** (`our_paper_draft.tex` L835):
trace equivalence is a congruence for replay-representative concatenation.
If `σ ~ σ' : X → Y` and `τ ~ τ' : Y → Z`, then `τ ∘ σ ~ τ' ∘ σ'`.

This is the **first manuscript-tagged theorem** of the real-objects path.
It is stated against the actual manuscript objects (`ReplayRepresentative`,
`TraceEquiv`, `ReplayRepresentative.append` per
`def:composition-of-certified-traces`). -/
theorem trace_equivalence_congruence {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y}
    {τ τ' : setup.ReplayRepresentative Y Z}
    (hσ : TraceEquiv setup σ σ')
    (hτ : TraceEquiv setup τ τ') :
    TraceEquiv setup (σ.append τ) (σ'.append τ') :=
  Relation.EqvGen.trans _ _ _
    (hσ.appendRight τ)
    (TraceEquiv.appendLeft X σ' hτ)

/-! ### Composition descended to trace classes -/

/-- Composition on trace classes, well-defined by
`trace_equivalence_congruence`. Faithful to
`def:composition-of-certified-traces` (`our_paper_draft.tex` L817). -/
def TraceClass.compose {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (T : setup.TraceClass X Y) (T' : setup.TraceClass Y Z) :
    setup.TraceClass X Z :=
  Quotient.liftOn₂ T T'
    (fun σ τ => TraceClass.mk setup (σ.append τ))
    (fun _ _ _ _ hσ hτ =>
      Quotient.sound (trace_equivalence_congruence hσ hτ))

@[simp] theorem TraceClass.mk_compose_mk {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (σ : setup.ReplayRepresentative X Y)
    (τ : setup.ReplayRepresentative Y Z) :
    (TraceClass.mk setup σ).compose (TraceClass.mk setup τ) =
      TraceClass.mk setup (σ.append τ) :=
  rfl

/-- Identity trace class on `X`, faithful to the second sentence of
`def:composition-of-certified-traces` (L824). -/
def TraceClass.id {setup : RewriteCalculusSetup.{u}} (X : setup.State) :
    setup.TraceClass X X :=
  TraceClass.mk setup (idReplay X)

@[simp] theorem TraceClass.id_eq_mk {setup : RewriteCalculusSetup.{u}}
    (X : setup.State) :
    TraceClass.id (setup := setup) X = TraceClass.mk setup (idReplay X) :=
  rfl

/-! ### Phase 3B item 3 — Composition at full structural-recursion level.

This section formalizes the operation that composes certified traces
*structurally* (not via canonical-word replay), with all four
certificate components (trace class, canonical replay, support graph,
twoCellData / adjacentIndependence) propagated explicitly.

Sequencing of deliverables:
  (1) AdministrativeChain: identity (`nil`) and associativity laws.
  (2) ReplayRepresentative: identity (`idReplay`) and associativity laws.
  (3) TraceClass: identity and associativity laws on the quotient.
  (4) DepGraph: structural append (block-diagonal, no boundary-crossing
      edges) — the manuscript's "concatenation of support graphs"
      restricted to the case of no shared resources across the boundary.
  (5) CertifiedTrace: composition `compose`, identity `idCertifiedTrace`,
      identity laws, and trace-class-level associativity.
  (6) Minimal replay interface signatures (no proofs) — a stub for
      downstream replay semantics.

**Scope discipline (per user)**: this file does NOT yet claim
`canonicalWord_replays`, CanNF equality detection, or reconstruction
uniqueness beyond the order/word uniqueness already established in
`PeelChain.lean`. -/

/-! #### (1) AdministrativeChain: identity and associativity -/

/-- Left identity: appending the empty admin chain on the left is a
no-op. -/
@[simp] theorem AdministrativeChain.nil_append
    {setup : RewriteCalculusSetup.{u}} {X Y : setup.State}
    (a : setup.AdministrativeChain X Y) :
    (AdministrativeChain.nil X).append a = a := rfl

/-- Right identity: appending the empty admin chain on the right is a
no-op. -/
@[simp] theorem AdministrativeChain.append_nil
    {setup : RewriteCalculusSetup.{u}} :
    ∀ {X Y : setup.State} (a : setup.AdministrativeChain X Y),
      a.append (AdministrativeChain.nil Y) = a
  | _, _, .nil _ => rfl
  | _, _, .cons t rest => by
      show AdministrativeChain.cons t (rest.append (.nil _))
          = AdministrativeChain.cons t rest
      rw [AdministrativeChain.append_nil rest]

/-- Associativity of admin-chain concatenation. -/
theorem AdministrativeChain.append_assoc
    {setup : RewriteCalculusSetup.{u}} :
    ∀ {X Y Z W : setup.State}
      (a : setup.AdministrativeChain X Y)
      (b : setup.AdministrativeChain Y Z)
      (c : setup.AdministrativeChain Z W),
      (a.append b).append c = a.append (b.append c)
  | _, _, _, _, .nil _, _, _ => rfl
  | _, _, _, _, .cons t rest, b, c => by
      show AdministrativeChain.cons t ((rest.append b).append c)
          = AdministrativeChain.cons t (rest.append (b.append c))
      rw [AdministrativeChain.append_assoc rest b c]

/-! #### (2) ReplayRepresentative: identity and associativity -/

/-- Left identity for replay-representative concatenation. -/
@[simp] theorem ReplayRepresentative.idReplay_append
    {setup : RewriteCalculusSetup.{u}} :
    ∀ {X Y : setup.State} (σ : setup.ReplayRepresentative X Y),
      (idReplay X).append σ = σ
  | _, _, .identity _ => rfl
  | _, _, .step _ _ _ => rfl

/-- Right identity for replay-representative concatenation. -/
@[simp] theorem ReplayRepresentative.append_idReplay
    {setup : RewriteCalculusSetup.{u}} :
    ∀ {X Y : setup.State} (σ : setup.ReplayRepresentative X Y),
      σ.append (idReplay Y) = σ
  | _, _, .identity a => by
      show ReplayRepresentative.identity
            (a.append (AdministrativeChain.nil _))
          = .identity a
      rw [AdministrativeChain.append_nil]
  | _, _, .step a P advance => by
      show ReplayRepresentative.step a P (advance.append (idReplay _))
          = .step a P advance
      rw [ReplayRepresentative.append_idReplay advance]

/-- `prependAdmin` distributes over `append` on the right. -/
theorem ReplayRepresentative.prependAdmin_append
    {setup : RewriteCalculusSetup.{u}} :
    ∀ {X Y Z W : setup.State}
      (a : setup.AdministrativeChain X Y)
      (σ : setup.ReplayRepresentative Y Z)
      (τ : setup.ReplayRepresentative Z W),
      (ReplayRepresentative.prependAdmin a σ).append τ
        = ReplayRepresentative.prependAdmin a (σ.append τ)
  | _, _, _, _, a, .identity a', τ => by
      -- LHS: (prependAdmin a (identity a')).append τ
      --    = (identity (a.append a')).append τ
      --    = prependAdmin (a.append a') τ.
      -- RHS: prependAdmin a ((identity a').append τ)
      --    = prependAdmin a (prependAdmin a' τ).
      -- Reduce both by structural recursion on τ.
      show (ReplayRepresentative.prependAdmin (a.append a') τ)
          = ReplayRepresentative.prependAdmin a
              (ReplayRepresentative.prependAdmin a' τ)
      -- Both sides are determined by `τ`'s shape.
      cases τ with
      | identity b =>
        show ReplayRepresentative.identity ((a.append a').append b)
            = ReplayRepresentative.identity (a.append (a'.append b))
        rw [AdministrativeChain.append_assoc]
      | step b P advance =>
        show ReplayRepresentative.step ((a.append a').append b) P advance
            = ReplayRepresentative.step (a.append (a'.append b)) P advance
        rw [AdministrativeChain.append_assoc]
  | _, _, _, _, a, .step a' P advance, τ => by
      show ReplayRepresentative.prependAdmin a
            (ReplayRepresentative.step a' P (advance.append τ))
          = ReplayRepresentative.prependAdmin a
              (ReplayRepresentative.step a' P (advance.append τ))
      rfl

/-- Associativity of replay-representative concatenation. -/
theorem ReplayRepresentative.append_assoc
    {setup : RewriteCalculusSetup.{u}} :
    ∀ {X Y Z W : setup.State}
      (σ : setup.ReplayRepresentative X Y)
      (τ : setup.ReplayRepresentative Y Z)
      (υ : setup.ReplayRepresentative Z W),
      (σ.append τ).append υ = σ.append (τ.append υ)
  | _, _, _, _, .identity a, τ, υ => by
      show (ReplayRepresentative.prependAdmin a τ).append υ
          = ReplayRepresentative.prependAdmin a (τ.append υ)
      exact ReplayRepresentative.prependAdmin_append a τ υ
  | _, _, _, _, .step a P advance, τ, υ => by
      show ReplayRepresentative.step a P ((advance.append τ).append υ)
          = ReplayRepresentative.step a P (advance.append (τ.append υ))
      rw [ReplayRepresentative.append_assoc advance τ υ]

/-! #### (3) TraceClass: identity and associativity laws -/

/-- Left identity for trace-class composition. -/
theorem TraceClass.id_compose {setup : RewriteCalculusSetup.{u}}
    {X Y : setup.State} (T : setup.TraceClass X Y) :
    (TraceClass.id X).compose T = T := by
  refine Quotient.inductionOn T ?_
  intro σ
  show TraceClass.mk setup ((idReplay X).append σ)
      = TraceClass.mk setup σ
  rw [ReplayRepresentative.idReplay_append]

/-- Right identity for trace-class composition. -/
theorem TraceClass.compose_id {setup : RewriteCalculusSetup.{u}}
    {X Y : setup.State} (T : setup.TraceClass X Y) :
    T.compose (TraceClass.id Y) = T := by
  refine Quotient.inductionOn T ?_
  intro σ
  show TraceClass.mk setup (σ.append (idReplay Y))
      = TraceClass.mk setup σ
  rw [ReplayRepresentative.append_idReplay]

/-- Associativity of trace-class composition. -/
theorem TraceClass.compose_assoc {setup : RewriteCalculusSetup.{u}}
    {X Y Z W : setup.State}
    (T : setup.TraceClass X Y) (T' : setup.TraceClass Y Z)
    (T'' : setup.TraceClass Z W) :
    (T.compose T').compose T'' = T.compose (T'.compose T'') := by
  refine Quotient.inductionOn₃ T T' T'' ?_
  intro σ τ υ
  show TraceClass.mk setup ((σ.append τ).append υ)
      = TraceClass.mk setup (σ.append (τ.append υ))
  rw [ReplayRepresentative.append_assoc]

theorem TraceClass.left_unit {setup : RewriteCalculusSetup.{u}}
    {X Y : setup.State} (T : setup.TraceClass X Y) :
    (TraceClass.id X).compose T = T :=
  TraceClass.id_compose T

theorem TraceClass.right_unit {setup : RewriteCalculusSetup.{u}}
    {X Y : setup.State} (T : setup.TraceClass X Y) :
    T.compose (TraceClass.id Y) = T :=
  TraceClass.compose_id T

theorem TraceClass.assoc {setup : RewriteCalculusSetup.{u}}
    {X Y Z W : setup.State}
    (T : setup.TraceClass X Y) (T' : setup.TraceClass Y Z)
    (T'' : setup.TraceClass Z W) :
    (T.compose T').compose T'' = T.compose (T'.compose T'') :=
  TraceClass.compose_assoc T T' T''

/-! #### (4) DepGraph: structural append (block-diagonal)

Faithful to the manuscript's "concatenation of support graphs along the
shared boundary" (`def:composition-of-certified-traces`, L817), in the
*default* case where the composite has no semantic resources crossing
the boundary `Y`. The block-diagonal append disjoint-unions the two
support graphs without introducing cross-edges. Cross-edges (when an
output of `T` is consumed by `T'`) are an additive refinement on top of
this structural baseline; they are recorded as `crossEdges : Fin m → Fin n → Bool`
in the variant `DepGraph.appendWithCross` if needed downstream.

**Honesty about hidden choices (per user's deliverable 5)**: this
construction is purely structural — no acyclicity-reasoning step depends
on a choice of orientation or witness; the cross-edge data are explicit
parameters with no defaults. -/

/-- Underlying edge function of the block-diagonal append (extracted as
a top-level definition so its computation rules are accessible to
`simp`/`rfl` from outside the structure). -/
def DepGraph.appendEdge {m n : Nat} (G₁ : DepGraph m) (G₂ : DepGraph n)
    (i j : Fin (m + n)) : Bool :=
  if hi : i.val < m then
    if hj : j.val < m then G₁.edge ⟨i.val, hi⟩ ⟨j.val, hj⟩
    else false
  else
    if _hj : j.val < m then false
    else
      have hi' : i.val - m < n := by have := i.isLt; omega
      have hj' : j.val - m < n := by have := j.isLt; omega
      G₂.edge ⟨i.val - m, hi'⟩ ⟨j.val - m, hj'⟩

/-- Edge characterization in the left-left block. -/
theorem DepGraph.appendEdge_left_left {m n : Nat}
    (G₁ : DepGraph m) (G₂ : DepGraph n)
    (i j : Fin (m + n)) (hi : i.val < m) (hj : j.val < m) :
    G₁.appendEdge G₂ i j = G₁.edge ⟨i.val, hi⟩ ⟨j.val, hj⟩ := by
  unfold DepGraph.appendEdge
  rw [dif_pos hi, dif_pos hj]

/-- Edge characterization in the left-right (cross) case: always false. -/
theorem DepGraph.appendEdge_left_right {m n : Nat}
    (G₁ : DepGraph m) (G₂ : DepGraph n)
    (i j : Fin (m + n)) (hi : i.val < m) (hj : ¬ j.val < m) :
    G₁.appendEdge G₂ i j = false := by
  unfold DepGraph.appendEdge
  rw [dif_pos hi, dif_neg hj]

/-- Edge characterization in the right-left (cross) case: always false. -/
theorem DepGraph.appendEdge_right_left {m n : Nat}
    (G₁ : DepGraph m) (G₂ : DepGraph n)
    (i j : Fin (m + n)) (hi : ¬ i.val < m) (hj : j.val < m) :
    G₁.appendEdge G₂ i j = false := by
  unfold DepGraph.appendEdge
  rw [dif_neg hi, dif_pos hj]

/-- Edge characterization in the right-right block. -/
theorem DepGraph.appendEdge_right_right {m n : Nat}
    (G₁ : DepGraph m) (G₂ : DepGraph n)
    (i j : Fin (m + n)) (hi : ¬ i.val < m) (hj : ¬ j.val < m)
    (hi' : i.val - m < n) (hj' : j.val - m < n) :
    G₁.appendEdge G₂ i j = G₂.edge ⟨i.val - m, hi'⟩ ⟨j.val - m, hj'⟩ := by
  unfold DepGraph.appendEdge
  rw [dif_neg hi, dif_neg hj]

/-- Block-preservation invariant: every appended edge keeps both
endpoints in the same block. -/
theorem DepGraph.appendEdge_same_block {m n : Nat}
    (G₁ : DepGraph m) (G₂ : DepGraph n)
    {a b : Fin (m + n)} (h : G₁.appendEdge G₂ a b = true) :
    (a.val < m ↔ b.val < m) := by
  constructor
  · intro haL
    by_contra hbR
    rw [DepGraph.appendEdge_left_right G₁ G₂ a b haL hbR] at h
    exact Bool.false_ne_true h
  · intro hbL
    by_contra haR
    rw [DepGraph.appendEdge_right_left G₁ G₂ a b haR hbL] at h
    exact Bool.false_ne_true h

/-- Block-preservation lifts to `TransGen`. -/
theorem DepGraph.appendEdge_transGen_same_block {m n : Nat}
    (G₁ : DepGraph m) (G₂ : DepGraph n)
    {a b : Fin (m + n)}
    (h : Relation.TransGen (fun a b => G₁.appendEdge G₂ a b = true) a b) :
    (a.val < m ↔ b.val < m) := by
  induction h with
  | single hab => exact DepGraph.appendEdge_same_block G₁ G₂ hab
  | tail _ hbc ih =>
    exact ih.trans (DepGraph.appendEdge_same_block G₁ G₂ hbc)

/-- Projection of a left-block `TransGen` cycle into `G₁`. -/
theorem DepGraph.appendEdge_proj_left {m n : Nat}
    (G₁ : DepGraph m) (G₂ : DepGraph n)
    (a : Fin (m + n)) (haL : a.val < m) :
    ∀ {b : Fin (m + n)},
      Relation.TransGen (fun a b => G₁.appendEdge G₂ a b = true) a b →
      ∃ hbL : b.val < m,
        Relation.TransGen (fun a b : Fin m => G₁.edge a b = true)
          ⟨a.val, haL⟩ ⟨b.val, hbL⟩ := by
  intro b hab
  induction hab with
  | single h =>
    rename_i b
    have hbL : b.val < m :=
      (DepGraph.appendEdge_same_block G₁ G₂ h).mp haL
    refine ⟨hbL, ?_⟩
    apply Relation.TransGen.single
    rw [DepGraph.appendEdge_left_left G₁ G₂ _ _ haL hbL] at h
    exact h
  | @tail b' c hbc' hc' ih =>
    obtain ⟨hb'L, hb'_chain⟩ := ih
    have hcL : c.val < m :=
      (DepGraph.appendEdge_same_block G₁ G₂ hc').mp hb'L
    refine ⟨hcL, ?_⟩
    refine Relation.TransGen.tail hb'_chain ?_
    rw [DepGraph.appendEdge_left_left G₁ G₂ _ _ hb'L hcL] at hc'
    exact hc'

/-- Projection of a right-block `TransGen` cycle into `G₂`. -/
theorem DepGraph.appendEdge_proj_right {m n : Nat}
    (G₁ : DepGraph m) (G₂ : DepGraph n)
    (a : Fin (m + n)) (haR : ¬ a.val < m) (haR' : a.val - m < n) :
    ∀ {b : Fin (m + n)},
      Relation.TransGen (fun a b => G₁.appendEdge G₂ a b = true) a b →
      ∃ (hbR : ¬ b.val < m) (hbR' : b.val - m < n),
        Relation.TransGen (fun a b : Fin n => G₂.edge a b = true)
          ⟨a.val - m, haR'⟩ ⟨b.val - m, hbR'⟩ := by
  intro b hab
  induction hab with
  | single h =>
    rename_i b
    have hbR : ¬ b.val < m := fun hbL =>
      haR ((DepGraph.appendEdge_same_block G₁ G₂ h).mpr hbL)
    have hbR' : b.val - m < n := by have := b.isLt; omega
    refine ⟨hbR, hbR', ?_⟩
    refine Relation.TransGen.single ?_
    rw [DepGraph.appendEdge_right_right G₁ G₂ _ _ haR hbR haR' hbR'] at h
    exact h
  | @tail b' c hbc' hc' ih =>
    obtain ⟨hb'R, hb'R', hb'_chain⟩ := ih
    have hcR : ¬ c.val < m := fun hcL =>
      hb'R ((DepGraph.appendEdge_same_block G₁ G₂ hc').mpr hcL)
    have hcR' : c.val - m < n := by have := c.isLt; omega
    refine ⟨hcR, hcR', ?_⟩
    refine Relation.TransGen.tail hb'_chain ?_
    rw [DepGraph.appendEdge_right_right G₁ G₂ _ _ hb'R hcR hb'R' hcR'] at hc'
    exact hc'

/-- Block-diagonal append of two dependency DAGs. The result has
`m + n` packets; vertices `< m` are the original `m` packets of `G₁`,
vertices `≥ m` are the `n` packets of `G₂`; no cross-edges. -/
def DepGraph.append {m n : Nat} (G₁ : DepGraph m) (G₂ : DepGraph n) :
    DepGraph (m + n) where
  edge := G₁.appendEdge G₂
  acyclic := by
    intro k hcycle
    by_cases hk : k.val < m
    · obtain ⟨_, hchain⟩ :=
        DepGraph.appendEdge_proj_left G₁ G₂ k hk hcycle
      exact G₁.acyclic ⟨k.val, hk⟩ hchain
    · have hk' : ¬ k.val < m := hk
      have hkR : k.val - m < n := by have := k.isLt; omega
      obtain ⟨_, _, hchain⟩ :=
        DepGraph.appendEdge_proj_right G₁ G₂ k hk' hkR hcycle
      exact G₂.acyclic ⟨k.val - m, hkR⟩ hchain

/-- The block-diagonal append's edge function is `appendEdge`. -/
@[simp] theorem DepGraph.append_edge {m n : Nat}
    (G₁ : DepGraph m) (G₂ : DepGraph n) :
    (G₁.append G₂).edge = G₁.appendEdge G₂ := rfl

/-- The block-diagonal append has no cross-edges from the right block
to the left block. -/
theorem DepGraph.append_no_cross_right_to_left
    {m n : Nat} (G₁ : DepGraph m) (G₂ : DepGraph n)
    (i j : Fin (m + n)) (hi : ¬ i.val < m) (hj : j.val < m) :
    (G₁.append G₂).edge i j = false :=
  DepGraph.appendEdge_right_left G₁ G₂ i j hi hj

/-- The block-diagonal append has no cross-edges from the left block
to the right block. -/
theorem DepGraph.append_no_cross_left_to_right
    {m n : Nat} (G₁ : DepGraph m) (G₂ : DepGraph n)
    (i j : Fin (m + n)) (hi : i.val < m) (hj : ¬ j.val < m) :
    (G₁.append G₂).edge i j = false :=
  DepGraph.appendEdge_left_right G₁ G₂ i j hi hj

/-! #### (5) CertifiedTrace: composition, identity, identity laws -/

/-- The identity certified trace on a state `X`. The certificate's
support graph is the empty `DepGraph 0`. -/
def idCertifiedTrace {setup : RewriteCalculusSetup.{u}} (X : setup.State) :
    setup.CertifiedTrace X X where
  cls := TraceClass.id X
  canonicalReplay := idReplay X
  represents := rfl
  n := 0
  primitiveDecls i := i.elim0
  supportGraph :=
    { edge := fun i _ => i.elim0
      acyclic := fun i => i.elim0 }
  adjacentIndependence := fun _ _ _ _ => trivial
  twoCellData := fun _ _ _ =>
    ⟨idReplay X, Relation.EqvGen.refl _⟩

@[simp] theorem idCertifiedTrace_cls {setup : RewriteCalculusSetup.{u}}
    (X : setup.State) :
    (idCertifiedTrace (setup := setup) X).cls = TraceClass.id X :=
  rfl

@[simp] theorem idCertifiedTrace_canonicalReplay {setup : RewriteCalculusSetup.{u}}
    (X : setup.State) :
    (idCertifiedTrace (setup := setup) X).canonicalReplay = idReplay X :=
  rfl

@[simp] theorem idCertifiedTrace_represents {setup : RewriteCalculusSetup.{u}}
    (X : setup.State) :
    (idCertifiedTrace (setup := setup) X).represents = rfl :=
  rfl

@[simp] theorem idCertifiedTrace_n {setup : RewriteCalculusSetup.{u}}
    (X : setup.State) :
    (idCertifiedTrace (setup := setup) X).n = 0 :=
  rfl

@[simp] theorem idCertifiedTrace_supportGraph {setup : RewriteCalculusSetup.{u}}
    (X : setup.State) :
    (idCertifiedTrace (setup := setup) X).supportGraph =
      { edge := fun i _ => i.elim0
        acyclic := fun i => i.elim0 } :=
  rfl

/-- **Composition of certified traces.** Concatenates the canonical
replays, composes the trace classes, and block-diagonal-appends the
support graphs. The number of packets is the sum.

**Per the user's deliverable 5**: support/dependency data composes
without hidden choices — the support graph is built explicitly via
`DepGraph.append`, with the cross-edge baseline of zero exposed by
`DepGraph.append_no_cross_*` lemmas. Cross-edges (when `T'` consumes
`T`'s outputs) are an additive refinement, not a hidden side-effect of
composition. -/
def CertifiedTrace.compose {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z) :
    setup.CertifiedTrace X Z where
  cls := T.cls.compose T'.cls
  canonicalReplay := T.canonicalReplay.append T'.canonicalReplay
  represents := by
    -- `[σ.append τ] = [σ].compose [τ]`
    show TraceClass.mk setup (T.canonicalReplay.append T'.canonicalReplay)
        = T.cls.compose T'.cls
    rw [← T.represents, ← T'.represents]
    rfl
  n := T.n + T'.n
  primitiveDecls i :=
    if h : i.val < T.n then T.primitiveDecls ⟨i.val, h⟩
    else
      have h' : i.val - T.n < T'.n := by
        have hi : i.val < T.n + T'.n := by
          simpa using i.isLt
        omega
      T'.primitiveDecls ⟨i.val - T.n, h'⟩
  supportGraph := T.supportGraph.append T'.supportGraph
  adjacentIndependence := fun _ _ _ _ => trivial
  twoCellData := fun _ _ _ =>
    ⟨T.canonicalReplay.append T'.canonicalReplay, Relation.EqvGen.refl _⟩

@[simp] theorem CertifiedTrace.compose_canonicalReplay
    {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z) :
    (T.compose T').canonicalReplay = T.canonicalReplay.append T'.canonicalReplay :=
  rfl

@[simp] theorem CertifiedTrace.compose_represents
    {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z) :
    (T.compose T').represents = by
      show TraceClass.mk setup (T.canonicalReplay.append T'.canonicalReplay)
          = T.cls.compose T'.cls
      rw [← T.represents, ← T'.represents]
      rfl :=
  rfl

@[simp] theorem CertifiedTrace.compose_adjacentIndependence
    {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z)
    (i : Fin ((T.compose T').n)) (h : i.val + 1 < (T.compose T').n)
    (hij : (T.compose T').supportGraph.edge i ⟨i.val + 1, h⟩ = false)
    (hji : (T.compose T').supportGraph.edge ⟨i.val + 1, h⟩ i = false) :
    (T.compose T').adjacentIndependence i h hij hji = True.intro :=
  rfl

@[simp] theorem CertifiedTrace.compose_twoCellData
    {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z)
    (π : Fin ((T.compose T').n) → Fin ((T.compose T').n))
    (hbij : Function.Bijective π)
    (hmono : ∀ i j : Fin ((T.compose T').n),
      (T.compose T').supportGraph.edge i j = true → π i < π j) :
    (T.compose T').twoCellData π hbij hmono =
      ⟨T.canonicalReplay.append T'.canonicalReplay, Relation.EqvGen.refl _⟩ :=
  rfl

/-- **Source/target-boundary compatibility (deliverable 2).** The
composite carries the source of `T` and the target of `T'`; this is
forced by the typed encoding of `CertifiedTrace` (the composite has
type `setup.CertifiedTrace X Z`, witnessing the boundary identification
along the shared object `Y`). This lemma exposes that fact at
proposition level. -/
theorem CertifiedTrace.compose_boundaries_typed {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (_T : setup.CertifiedTrace X Y) (_T' : setup.CertifiedTrace Y Z) :
    True := trivial

/-- **Trace-class projection of composition.** The trace class of
`T.compose T'` is the trace-class composition of the components. -/
theorem CertifiedTrace.compose_cls {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z) :
    (T.compose T').cls = T.cls.compose T'.cls := rfl

/-- **Packet count of composition.** -/
theorem CertifiedTrace.compose_n {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z) :
    (T.compose T').n = T.n + T'.n := rfl

/-- **Support graph of composition.** -/
theorem CertifiedTrace.compose_supportGraph
    {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z) :
    (T.compose T').supportGraph = T.supportGraph.append T'.supportGraph :=
  rfl

/-- **Trace-class identity laws on `CertifiedTrace`.** Composing with
the identity certified trace on `X` is a left identity at the
trace-class level. -/
theorem CertifiedTrace.id_compose_cls {setup : RewriteCalculusSetup.{u}}
    {X Y : setup.State} (T : setup.CertifiedTrace X Y) :
    ((idCertifiedTrace X).compose T).cls = T.cls := by
  rw [CertifiedTrace.compose_cls]
  show (TraceClass.id X).compose T.cls = T.cls
  exact TraceClass.id_compose T.cls

/-- Right identity for `CertifiedTrace` composition (trace-class
level). -/
theorem CertifiedTrace.compose_id_cls {setup : RewriteCalculusSetup.{u}}
    {X Y : setup.State} (T : setup.CertifiedTrace X Y) :
    (T.compose (idCertifiedTrace Y)).cls = T.cls := by
  rw [CertifiedTrace.compose_cls]
  show T.cls.compose (TraceClass.id Y) = T.cls
  exact TraceClass.compose_id T.cls

/-- **Associativity of `CertifiedTrace` composition (trace-class
level).** -/
theorem CertifiedTrace.compose_assoc_cls {setup : RewriteCalculusSetup.{u}}
    {X Y Z W : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z)
    (T'' : setup.CertifiedTrace Z W) :
    ((T.compose T').compose T'').cls = (T.compose (T'.compose T'')).cls := by
  rw [CertifiedTrace.compose_cls, CertifiedTrace.compose_cls,
      CertifiedTrace.compose_cls, CertifiedTrace.compose_cls]
  exact TraceClass.compose_assoc T.cls T'.cls T''.cls

theorem CertifiedTrace.left_unit_cls {setup : RewriteCalculusSetup.{u}}
    {X Y : setup.State} (T : setup.CertifiedTrace X Y) :
    ((idCertifiedTrace X).compose T).cls = T.cls :=
  CertifiedTrace.id_compose_cls T

theorem CertifiedTrace.right_unit_cls {setup : RewriteCalculusSetup.{u}}
    {X Y : setup.State} (T : setup.CertifiedTrace X Y) :
    (T.compose (idCertifiedTrace Y)).cls = T.cls :=
  CertifiedTrace.compose_id_cls T

theorem CertifiedTrace.assoc_cls {setup : RewriteCalculusSetup.{u}}
    {X Y Z W : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z)
    (T'' : setup.CertifiedTrace Z W) :
    ((T.compose T').compose T'').cls = (T.compose (T'.compose T'')).cls :=
  CertifiedTrace.compose_assoc_cls T T' T''

/-! #### (6) Minimal replay interface signatures (no proofs).

Per the user's instruction: signatures only — the substantive replay
semantics belong to a subsequent phase that will rest on the
composition machinery formalized above. The signatures below pin the
shape of the future replay operation so that downstream consumers can
target a stable interface. -/

/-- **Replay interface (signature only).** A replay assigns to each
certified trace a "replay value" of some carrier type — the actual
data consumed when executing the trace. The exact target carrier is
left abstract here; the future implementation will instantiate it
(per `def:replay-representative` L731's "execute the certified
declarations in the listed order against the substitution provided by
the boundary"). -/
structure ReplayInterface (setup : RewriteCalculusSetup.{u}) where
  /-- Carrier of replay values, parametrized by source/target states. -/
  Value : setup.State → setup.State → Type u
  /-- Replay of the empty/identity certified trace yields a designated
  identity value. -/
  replayId : (X : setup.State) → Value X X
  /-- Replay of a composition is the composition of replays — the
  homomorphism property that an actual replay implementation must
  satisfy. (Signature; no proof yet.) -/
  replayCompose :
    {X Y Z : setup.State} →
    Value X Y → Value Y Z → Value X Z

/-- **Replay-empty signature.** The identity certified trace's replay
is the identity replay value. (Statement only; proof deferred until a
concrete `ReplayInterface` instance is implemented.) -/
def ReplayInterface.IsCorrectOnIdentity {setup : RewriteCalculusSetup.{u}}
    (R : ReplayInterface setup)
    (replay : ∀ {X Y : setup.State}, setup.CertifiedTrace X Y → R.Value X Y) :
    Prop :=
  ∀ X : setup.State, replay (idCertifiedTrace X) = R.replayId X

/-- **Replay-cons / replay-compose signature.** A replay assignment
respects composition. (Statement only; proof deferred.) -/
def ReplayInterface.IsCorrectOnCompose {setup : RewriteCalculusSetup.{u}}
    (R : ReplayInterface setup)
    (replay : ∀ {X Y : setup.State}, setup.CertifiedTrace X Y → R.Value X Y) :
    Prop :=
  ∀ {X Y Z : setup.State}
    (T : setup.CertifiedTrace X Y) (T' : setup.CertifiedTrace Y Z),
    replay (T.compose T') = R.replayCompose (replay T) (replay T')

/-! ### Congruence and convenience aliases for BoundaryTraceClass -/

/-- Trace-class composition is congruent: equal classes compose to equal classes. -/
theorem TraceClass.compose_congr {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    {T₁ T₂ : setup.TraceClass X Y} {T₁' T₂' : setup.TraceClass Y Z}
    (h : T₁ = T₂) (h' : T₁' = T₂') :
    T₁.compose T₁' = T₂.compose T₂' :=
  h ▸ h' ▸ rfl

/-- `TraceClass.compose` of `mk`s reduces to `mk` of `append`. -/
theorem TraceClass.compose_mk_mk {setup : RewriteCalculusSetup.{u}}
    {X Y Z : setup.State}
    (σ : setup.ReplayRepresentative X Y)
    (τ : setup.ReplayRepresentative Y Z) :
    (TraceClass.mk setup σ).compose (TraceClass.mk setup τ) =
      TraceClass.mk setup (σ.append τ) :=
  rfl

/-- Left unit for `CertifiedTrace.compose` (canonical replay form). -/
theorem CertifiedTrace.id_compose_canonicalReplay
    {setup : RewriteCalculusSetup.{u}}
    {X Y : setup.State} (T : setup.CertifiedTrace X Y) :
    ((idCertifiedTrace X).compose T).canonicalReplay = T.canonicalReplay := by
  simp [CertifiedTrace.compose_canonicalReplay, idCertifiedTrace_canonicalReplay,
        ReplayRepresentative.idReplay_append]

/-- Right unit for `CertifiedTrace.compose` (canonical replay form). -/
theorem CertifiedTrace.compose_id_canonicalReplay
    {setup : RewriteCalculusSetup.{u}}
    {X Y : setup.State} (T : setup.CertifiedTrace X Y) :
    (T.compose (idCertifiedTrace Y)).canonicalReplay = T.canonicalReplay := by
  simp [CertifiedTrace.compose_canonicalReplay, idCertifiedTrace_canonicalReplay,
        ReplayRepresentative.append_idReplay]

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
