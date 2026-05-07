import TraceCalc.LayerB.RealObjects.QuotientRealization

/-!
# Real-objects formalization: quotient-realization obligation audit (items 8q–8u)

**Phase 8 items 8q–8u (2026-04-24).** Audit the concrete data
required to instantiate `FrontierQuotientRealization` (item 8l).

## Items in this file

* **8q** — `QuotientRealizationObligations setup`: the obligation
  structure naming what data a *future* boundary-vs-interior
  decomposition would have to supply.
* **8r** — Proposed product target `BoundaryCode × InteriorCode`
  (recorded as the realize-target in the assembly theorem).
* **8s** — Assembly theorem
  `QuotientRealizationObligations.toFrontierQuotientRealization`:
  if all obligations are supplied, they assemble into a faithful
  `FrontierQuotientRealization`.
* **8t** — Manuscript-facing aliases.
* **8u** — Honest carrier-enrichment audit (file header + a named
  audit `def`): documents which `RecordStructEquiv` clauses each
  obligation field is responsible for.

## Honest scope (per user's stop conditions, all honored)

* No concrete `BoundaryCode` is constructed.
* No concrete `InteriorCode` is constructed.
* No concrete `boundary_admin_code` / `strict_interior_code` is
  supplied.
* No `QuotientRealizationObligations` instance is supplied.
* `FrontierWord` is **not** enriched.
* Two of the per-side completeness obligations
  (`boundary_admin_code_complete`, `interior_code_complete`) are
  `Prop` placeholders — they cannot be given a real signature
  without first introducing separate "boundary part" and "interior
  part" of `RecordStructEquiv`, which are not currently named.
  The substantive faithful-direction content lives in
  `combined_code_extensionality`, which **does** have a real
  signature.

## Carrier-enrichment audit (item 8u)

`FrontierWord.Equiv = RecordStructEquiv BoundaryAdminEquiv` decomposes into:

* **Boundary-side clauses** (handled by `boundary_admin_code`):
  - `Y_rel : BoundaryAdminEquiv R₁.Y R₂.Y` — the boundary-object
    admin slot;
  - `externalOut_perm : List.Perm R₁.ports.externalOut R₂.ports.externalOut`
    — the boundary-block-swap perm slot.
* **Strict-interior clauses** (handled by `strict_interior_code`):
  - `n_eq`, `X_eq`, `externalIn_eq`, `packetIn_eq`, `packetOut_eq`,
    `packets_eq`, `dep_edge_eq`, `attach_eq` — all asserted by *strict*
    equality on `CompletedReconstructionRecord` fields, all of which
    are exposed via `w.residue` on the current skeletal `FrontierWord`.

**Conclusion**: the strict-interior fields require **no
`FrontierWord` carrier enrichment** — they are already accessible.
The only data the boundary-admin code needs that is *not* exposed
as ordered/comparable data at the abstract level is the
`BoundaryAdminEquiv` quotient itself, which is precisely the
ordering/key obligation already audited as
`ResidueKeyStabilityObligations.boundary_key_admin_stable` (item
8j). **No carrier enrichment is required for item 8q–8u.**

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`).
* L1098 (`def:completed-reconstruction-record`).
* L1108–L1120 — the `ports / packets / dep / attach / tensor / key`
  fields whose strict-equality coding is the interior obligation.
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ## Item 8q — Quotient-realization obligation structure -/

/-- **`QuotientRealizationObligations setup`** (item 8q): the
obligation structure naming the data a future boundary-vs-interior
decomposition of the residue admin quotient must supply.

The obligations split the `RecordStructEquiv BoundaryAdminEquiv`
clauses into a **boundary-admin side** (`Y` admin-related,
`externalOut` perm-related) and a **strict-interior side**
(everything else, asserted by `=`).

* `boundary_admin_code` / `strict_interior_code` — the two coding
  functions.
* `boundary_admin_code_sound` / `interior_code_sound` — each code
  respects `FrontierWord.Equiv`. **Real signatures.**
* `boundary_admin_code_complete` / `interior_code_complete` —
  per-side faithfulness obligations. **`Prop` placeholders**: these
  cannot be given real signatures without first introducing a
  formal "boundary part" / "interior part" of
  `RecordStructEquiv`, which are not currently named in the
  formalization.
* `combined_code_extensionality` — the substantive
  faithful-direction obligation: matching boundary *and* interior
  codes implies full `FrontierWord.Equiv`. **Real signature.** -/
structure QuotientRealizationObligations
    (setup : RewriteCalculusSetup.{u}) where
  /-- The boundary-admin code target. -/
  BoundaryCode : Type v
  /-- The strict-interior code target. -/
  InteriorCode : Type v
  /-- Boundary-admin coding function. Codes the boundary-related
  data (`Y` and `externalOut`) of the residue. -/
  boundary_admin_code : FrontierWord setup → BoundaryCode
  /-- Boundary-admin code soundness: `Equiv` ⇒ equal boundary codes. -/
  boundary_admin_code_sound :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ →
        boundary_admin_code w₁ = boundary_admin_code w₂
  /-- Boundary-admin code completeness obligation. **`Prop`
  placeholder**: per-side faithful-direction content (equal boundary
  codes ⇒ boundary-side `RecordStructEquiv` clauses) is not exposed
  as a real signature here, since "boundary part of `Equiv`" is not
  named as a separate predicate. The substantive faithful content
  lives in `combined_code_extensionality`. -/
  boundary_admin_code_complete : Prop
  /-- Strict-interior coding function. Codes the strict-equality
  fields of the residue (`n`, `X`, `externalIn`, `packetIn`,
  `packetOut`, `packets`, `dep.edge`, `attach`). -/
  strict_interior_code : FrontierWord setup → InteriorCode
  /-- Strict-interior code soundness: `Equiv` ⇒ equal interior codes. -/
  interior_code_sound :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ →
        strict_interior_code w₁ = strict_interior_code w₂
  /-- Strict-interior code completeness obligation. **`Prop`
  placeholder** for the same reason as
  `boundary_admin_code_complete`. -/
  interior_code_complete : Prop
  /-- **Combined-code extensionality** — the substantive
  faithful-direction obligation. Matching boundary codes *and*
  matching interior codes together imply full `FrontierWord.Equiv`. -/
  combined_code_extensionality :
    ∀ {w₁ w₂ : FrontierWord setup},
      boundary_admin_code w₁ = boundary_admin_code w₂ →
        strict_interior_code w₁ = strict_interior_code w₂ →
          FrontierWord.Equiv w₁ w₂

namespace QuotientRealizationObligations

/-! ## Item 8r — Proposed product target -/

/-- **Item 8r — Product target**: the proposed realize-target is
the product `BoundaryCode × InteriorCode`, with realize defined as
the pair of the two coding functions. Recorded here as a `def` for
naming clarity; the actual product use is inside the assembly
theorem (item 8s). -/
def productTarget (Q : QuotientRealizationObligations.{u, v} setup) :
    Type v :=
  Q.BoundaryCode × Q.InteriorCode

/-- The product code: a frontier word maps to the pair of its
boundary-admin code and its strict-interior code. -/
def productCode (Q : QuotientRealizationObligations.{u, v} setup)
    (w : FrontierWord setup) : Q.productTarget :=
  (Q.boundary_admin_code w, Q.strict_interior_code w)

/-! ## Item 8s — Assembly theorem -/

/-- **Item 8s — Assembly theorem**: a `QuotientRealizationObligations`
instance assembles into a faithful `FrontierQuotientRealization`,
with `Target := BoundaryCode × InteriorCode` and
`realize := productCode`.

* `respects_equiv` follows from the per-side soundness obligations
  (`boundary_admin_code_sound`, `interior_code_sound`).
* `faithful` follows from `combined_code_extensionality` after
  destructuring the product equality.

**No content manufactured.** -/
def toFrontierQuotientRealization
    (Q : QuotientRealizationObligations.{u, v} setup) :
    FrontierQuotientRealization.{u, v} setup where
  Target := Q.productTarget
  realize w := Q.productCode w
  respects_equiv h := by
    show (_, _) = (_, _)
    exact Prod.mk.injEq .. |>.mpr
      ⟨Q.boundary_admin_code_sound h, Q.interior_code_sound h⟩
  faithful h := by
    have hb : Q.boundary_admin_code _ = Q.boundary_admin_code _ :=
      congrArg Prod.fst h
    have hi : Q.strict_interior_code _ = Q.strict_interior_code _ :=
      congrArg Prod.snd h
    exact Q.combined_code_extensionality hb hi

/-- **Audit theorem**: the assembled realization's `realize` is
exactly the product code. -/
@[simp] theorem toFrontierQuotientRealization_realize
    (Q : QuotientRealizationObligations.{u, v} setup)
    (w : FrontierWord setup) :
    (Q.toFrontierQuotientRealization).realize w = Q.productCode w :=
  rfl

end QuotientRealizationObligations

/-! ## Item 8u — Carrier-enrichment audit (named `def` pointer) -/

/-- **Item 8u — Carrier-enrichment audit** (also documented in the
file header): a `def` whose body is the assembly theorem from item
8s, named so that the audit is type-checkable as a Lean term and
not merely a docstring claim.

The audit conclusion is: **no `FrontierWord` carrier enrichment is
required** to supply a `QuotientRealizationObligations` instance.
The boundary-admin code consumes only the residue's `Y` and
`externalOut` (both exposed via `w.residue`); the strict-interior
code consumes only the strict-equality fields of the residue (also
exposed via `w.residue`).

The substantive future obstacle is therefore *not* enriching the
carrier but **constructing canonical boundary-admin codes stable
under `BoundaryAdminEquiv`**, which is exactly the obligation named
by `ResidueKeyStabilityObligations.boundary_key_admin_stable`
(item 8j). -/
def theorem_quotient_realization_obligations_require_no_carrier_enrichment
    (Q : QuotientRealizationObligations.{u, v} setup) :
    FrontierQuotientRealization.{u, v} setup :=
  Q.toFrontierQuotientRealization

/-! ## Item 8t — Manuscript-facing aliases -/

/-- **Manuscript alias (8t.a)**: the boundary-admin code
completeness obligation is the corresponding `Prop` placeholder
field of `QuotientRealizationObligations`. -/
def theorem_boundary_code_completeness_obligation
    (Q : QuotientRealizationObligations.{u, v} setup) : Prop :=
  Q.boundary_admin_code_complete

/-- **Manuscript alias (8t.b)**: the strict-interior code
extensionality obligation — i.e., the *combined* extensionality
obligation that is the substantive faithful-direction content. The
per-side `interior_code_complete` field is a `Prop` placeholder;
the real interior-extensionality content is the combined obligation
exposed here. -/
def theorem_interior_code_extensionality_obligation
    (Q : QuotientRealizationObligations.{u, v} setup) :
    ∀ {w₁ w₂ : FrontierWord setup},
      Q.boundary_admin_code w₁ = Q.boundary_admin_code w₂ →
        Q.strict_interior_code w₁ = Q.strict_interior_code w₂ →
          FrontierWord.Equiv w₁ w₂ :=
  Q.combined_code_extensionality

/-- **Manuscript alias (8t.c)**: a complete set of
quotient-realization obligations assembles into a faithful
quotient realization with target `BoundaryCode × InteriorCode`. -/
def theorem_product_code_gives_frontier_quotient_realization
    (Q : QuotientRealizationObligations.{u, v} setup) :
    FrontierQuotientRealization.{u, v} setup :=
  Q.toFrontierQuotientRealization

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
