import TraceCalc.LayerB.Foundations.Doctrine

/-!
# Foundational syntax: occurrences, replacement, primitive certified declarations

**Real-objects path, Lane B cycle 4 (2026-04-23).**

Builds the occurrence-rewrite-step layer on top of cycle 3's
`Doctrine` and the cycle 1–2 syntax.

## Manuscript correspondence

* `Ctx Sig sIn sOut` ↔ the *one-hole context* implicit in
  `def:typed-occurrence-map` (`our_paper_draft.tex` L587). The
  manuscript phrases an occurrence map as an injective sort/label/
  incidence-preserving function `μ : ℓ → C`. In the strict-tree
  encoding adopted in cycle 2 (`ExprCirquent` / `BoundaryCirquent`),
  this is exactly: a position inside one of `C`'s output expressions
  where `ℓ` (with its holes filled) appears as a sub-expression.
  The position is captured by a typed inductive `Ctx Sig sIn sOut`
  — a single-hole pattern of result sort `sOut` whose unique hole
  has sort `sIn`.
* `Ctx.fill` ↔ "plug the occurrence map into the ambient cirquent".
* `Occurrence` ↔ `def:occurrence` (L612): triple `(μ, (K_i), A)` of
  occurrence map + filler data + ambient attachment. In the
  strict-tree encoding the filler data are *exactly* a typed
  total filling `θ` for the holes of `ℓ`, and the "ambient parent
  attachment" is *exactly* the surrounding context `Ctx Sig ρ.outSort
  (G.outputProfile.get outIdx)` together with the choice of output
  index `outIdx`. The `match_witness` field is the manuscript's
  injectivity-and-typing condition: the occurrence `μ` actually maps
  the filled `ℓ` to the corresponding subterm of `C`.
* `replace` ↔ `def:replacement` (L618): substitute the instantiated
  right pattern through the same context.
* `PrimitiveCertifiedDeclaration` ↔ `def:primitive-certified-declaration`
  (L612): the four-tuple `(scheme, occurrence, support, certificate)`.
  Support data and replay certificate are intentionally carried as
  opaque types in this cycle, faithful to the manuscript's deferral
  to `def:primitive-support-payload` (L679) and the replay-certificate
  prose (L617).
* `applyStep` ↔ `def:one-step-rule-application` (L625): replaces the
  current goal and updates the env via the certificate's hook.
* `replacement_preserves_structure` ↔ `prop:replacement-preserves-structure`
  (L630).
* `replacement_preserves_acyclicity` ↔ `prop:replacement-preserves-acyclicity`
  (L639).
* `applyStep_preserves_wellformed` ↔
  `prop:one-step-rule-application-preserves-well-formedness` (L648).

## Encoding notes (carried honestly in code)

* The strict-tree reading of cirquents (cycle 2) makes finiteness,
  acyclicity, and typed sort-compatibility *automatic* dependent-type
  invariants. The three preservation propositions (L630, L639, L648)
  therefore reduce to either reflexivity or a one-step structural
  observation.
* Support data and replay certificates are opaque in this cycle.
  The manuscript treats their content as deferred to L679 and to the
  carrier (`def:carrier`, L429); we faithfully carry them as `Type u`
  parameters with a documented `envUpdate` hook on the certificate.
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace Foundations

variable {D : PrimitiveInterfaceData.{u}} {Sig : Signature D}

/-! ### One-hole contexts -/

/-- **One-hole context** of result sort `sOut` with the unique hole of
sort `sIn`. Faithful to `def:typed-occurrence-map`
(`our_paper_draft.tex` L587) under the strict-tree reading of the
cycle-2 cirquents.

Constructors:
* `hole` — the trivial context (the hole *is* the whole expression).
* `op ω k siblings focus` — apply operation symbol `ω` whose `k`-th
  input is the focused sub-context; the other inputs are concrete
  expressions supplied by `siblings`. -/
inductive Ctx {D : PrimitiveInterfaceData.{u}} (Sig : Signature D)
    (sIn : Sort_ D) : Sort_ D → Type u
  | hole : Ctx Sig sIn sIn
  | op (ω : Sig.Op) (k : Fin (Sig.opArity ω))
       (siblings : (i : Fin (Sig.opArity ω)) → i ≠ k → Expr Sig (Sig.opIn ω i))
       (focus : Ctx Sig sIn (Sig.opIn ω k)) :
       Ctx Sig sIn (Sig.opOut ω)

namespace Ctx

variable {D : PrimitiveInterfaceData.{u}} {Sig : Signature D}

/-- Fill the unique hole of a context with a typed expression. -/
def fill : {sIn sOut : Sort_ D} → Ctx Sig sIn sOut → Expr Sig sIn → Expr Sig sOut
  | _, _, .hole, e => e
  | _, _, .op ω k siblings focus, e =>
      Expr.op ω fun i =>
        if h : i = k then
          h ▸ focus.fill e
        else
          siblings i h

end Ctx

/-! ### Occurrences (`def:occurrence`, L612) -/

/-- **`def:occurrence`** (`our_paper_draft.tex` L612): a triple
`(μ, (K_i), A)` of an occurrence map of `ρ.lhs` into `G`, filler data
for the holes of `ρ.lhs`, and ambient parent-attachment data.

Strict-tree encoding (cf. file docstring):

* `outIdx` chooses which output of `G` carries the occurrence;
* `ctx` is the ambient parent-attachment data — the one-hole context
  surrounding the occurrence inside `G.outputs outIdx`;
* `θ` is the filler data — a typed total filling for `ρ.lhs`'s holes;
* `match_witness` is the manuscript's typing/incidence/injectivity
  condition: substituting `θ` into `ρ.lhs` and plugging into `ctx`
  reproduces `G.outputs outIdx`. -/
structure Occurrence (Dc : Doctrine D) (ρ : RewriteScheme Dc.sig)
    (G : Goal Dc.sig) where
  outIdx : Fin G.outputProfile.length
  /-- The shared output sort matches the chosen output. -/
  out_sort_eq : G.outputProfile.get outIdx = ρ.outSort
  /-- The ambient parent-attachment data: the one-hole context
  inside the chosen output at which `ρ.lhs[θ]` appears. -/
  ctx : Ctx Dc.sig ρ.outSort (G.outputProfile.get outIdx)
  /-- The filler data: a typed total filling for `ρ.lhs`'s holes. -/
  θ : (s : Sort_ D) → Dc.sig.Hole s → Expr Dc.sig s
  /-- The manuscript's typing/incidence/injectivity condition. -/
  match_witness : ctx.fill (ρ.lhs.plug θ) = G.outputs outIdx

/-! ### Replacement (`def:replacement`, L618) -/

/-- **`def:replacement`** (`our_paper_draft.tex` L618): replace the
occurrence's image by the instantiated right pattern.

In the strict-tree encoding, this is exactly: substitute
`ρ.rhs.plug θ` into the same one-hole context at the same output
index. -/
def replace {Dc : Doctrine D} {ρ : RewriteScheme Dc.sig}
    {G : Goal Dc.sig} (occ : Occurrence Dc ρ G) : Goal Dc.sig where
  inputProfile := G.inputProfile
  outputProfile := G.outputProfile
  inputVars := G.inputVars
  outputs := fun i =>
    if h : i = occ.outIdx then
      h ▸ occ.ctx.fill (ρ.rhs.plug occ.θ)
    else
      G.outputs i

/-! ### Primitive certified declarations (`def:primitive-certified-declaration`, L612) -/

/-- A **support payload** in this cycle is carried as an opaque
`Type u` parameter on a per-state basis, faithful to the manuscript's
deferral of its content to `def:primitive-support-payload`
(`our_paper_draft.tex` L679). -/
structure SupportPayloadData where
  /-- Opaque per-step support payload. -/
  payload : Type u

/-- A **replay certificate** carries (a) the witness package required
by `def:primitive-certified-declaration` (`our_paper_draft.tex` L617)
and (b) a hook `envUpdate` performing the administrative bookkeeping
update of `def:one-step-rule-application` (L625).

The witness package itself is opaque in this cycle (the manuscript
defers its content to the doctrine and the carrier); the env-update
hook is a real function. -/
structure ReplayCertificate (Dc : Doctrine D) where
  /-- Opaque admissibility witness. -/
  witness : Type u
  /-- Administrative env update of `def:one-step-rule-application`
  (L625). Faithful: the certificate decides how the env evolves. -/
  envUpdate : DefinitionEnvironment Dc.sig → DefinitionEnvironment Dc.sig

/-- **`def:primitive-certified-declaration`**
(`our_paper_draft.tex` L612): the four-tuple
`(ρ, occurrence, support, certificate)` on a state `S`. -/
structure PrimitiveCertifiedDeclaration (Dc : Doctrine D) (S : State Dc.sig) where
  /-- The rewrite scheme `ρ` (component (1) of L613). -/
  schemeIdx : Dc.R_index
  /-- The occurrence in the current goal (component (2) of L614). -/
  occurrence : Occurrence Dc (Dc.R schemeIdx) S.goal
  /-- Support data (component (3) of L616). Opaque per the manuscript's
  deferral to `def:primitive-support-payload` (L679). -/
  support : SupportPayloadData
  /-- Replay certificate (component (4) of L617). -/
  certificate : ReplayCertificate Dc

/-! ### One-step rule application (`def:one-step-rule-application`, L625) -/

/-- **`def:one-step-rule-application`** (`our_paper_draft.tex` L625):
applying a primitive certified declaration to a state produces a new
state by performing the replacement on the current goal and updating
the env via the certificate's bookkeeping. -/
def applyStep {Dc : Doctrine D} {S : State Dc.sig}
    (P : PrimitiveCertifiedDeclaration Dc S) : State Dc.sig where
  env := P.certificate.envUpdate S.env
  goal := replace P.occurrence

/-! ### Preservation propositions

The strict-tree encoding (cycle 2) makes finiteness, acyclicity, and
typed sort-compatibility automatic dependent-type invariants. The
three manuscript preservation propositions therefore have content
that is either reflexive or one-step structural. -/

/-- **`prop:replacement-preserves-structure`** (`our_paper_draft.tex`
L630): replacement preserves *(a)* finiteness, *(b)* sort
compatibility, and *(c)* the external boundary profile.

In the strict-tree encoding, finiteness and sort-compatibility are
dependent-type invariants of `Goal`/`Expr`/`Pat` (so already
discharged by typing), and the external boundary profile is preserved
because `replace` copies `inputProfile`, `outputProfile`, and
`inputVars` verbatim. -/
theorem replacement_preserves_structure
    {Dc : Doctrine D} {ρ : RewriteScheme Dc.sig} {G : Goal Dc.sig}
    (occ : Occurrence Dc ρ G) :
    (replace occ).inputProfile = G.inputProfile ∧
      (replace occ).outputProfile = G.outputProfile ∧
      ∀ i, (replace occ).inputVars i = G.inputVars i := by
  refine ⟨rfl, rfl, fun _ => rfl⟩

/-- **`prop:replacement-preserves-acyclicity`**
(`our_paper_draft.tex` L639): replacement at an admissible occurrence
yields an acyclic goal.

In the strict-tree encoding every output of `replace occ` is an
inductive `Expr`, which is automatically a finite acyclic typed tree.
We expose this explicitly. -/
theorem replacement_preserves_acyclicity
    {Dc : Doctrine D} {ρ : RewriteScheme Dc.sig} {G : Goal Dc.sig}
    (occ : Occurrence Dc ρ G) :
    ∀ i : Fin (replace occ).outputProfile.length,
      ∃ e : Expr Dc.sig ((replace occ).outputProfile.get i),
        (replace occ).outputs i = e := by
  intro i
  exact ⟨(replace occ).outputs i, rfl⟩

/-- **`prop:one-step-rule-application-preserves-well-formedness`**
(`our_paper_draft.tex` L648): a primitive certified step sends a
well-formed state to a well-formed state.

The goal half is controlled by `replacement_preserves_structure` and
`replacement_preserves_acyclicity`; the env half is the certificate's
admissible administrative move (`def:one-step-rule-application`,
L625). In the doctrine-aware refinement, env compatibility unfolds to
`EnvCompat.goalAllBound` after the env update. We supply both halves
*conditionally*: well-formedness propagates whenever the certificate's
`envUpdate` preserves binding, which is the manuscript's "admissible
administrative move" condition. -/
theorem applyStep_preserves_wellformed
    {Dc : Doctrine D} {S : State Dc.sig}
    (P : PrimitiveCertifiedDeclaration Dc S)
    (_h_goal_wf : Goal.IsWellFormedAt Dc S.goal)
    (h_env_preserves :
      EnvCompat.goalAllBound S.env.scope S.goal →
      EnvCompat.goalAllBound (P.certificate.envUpdate S.env).scope
        (replace P.occurrence))
    (h_state_wf : EnvCompat.goalAllBound S.env.scope S.goal) :
    State.IsWellFormedAt Dc (applyStep P) := by
  refine
    { goalWf := ?_
      envCompatibleWithGoal := h_env_preserves h_state_wf }
  -- Goal-side well-formedness: `Goal.IsWellFormedAt` reduces to
  -- `Goal.IsBoundaryCompatible`, which is reflexive in our encoding.
  exact ⟨Goal.isBoundaryCompatible_intro Dc (replace P.occurrence)⟩

end Foundations
end LayerB
end TraceCalc
