/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:748-801 (trace equivalence, trace class, certified trace)
- our_paper_draft.tex:1926-2088 (stabilization context where boundary triangles are consumed)
- our_paper_draft.tex:2130-2166 (minimal package and classical realization conditions for boundary outputs)
- our_paper_draft.tex:2501-2544 (comparison constraints on boundary-compatible morphisms)
- our_paper_draft.tex:5700-5714 (pi0 comparison by double representability, downstream trace-facing compatibility)

Still missing in this file/module:
- Complete TeX-label citations on every exported declaration (not only selected definitions).
- Explicit dependency edges from trace declarations to comparison/realization theorems.
- A theorem-by-theorem ledger mapping TR1--TR4 obligations to exact manuscript labels.

Coverage intent for this file:
- Preserve the current live boundary/triangulated structures.
- Use this header as the manuscript boundary-proof checklist until labels are attached per declaration.
-/

import MacLane.Trace.Certified

/-!
# Trace Boundary Structure

## Final-Form Policy

Boundary and triangulated constructions here must match their intended final
mathematical statements. Do not use toy or weakened substitutes for distinguished
triangle data or boundary reflection surfaces.

If a proof cannot be completed, isolate the exact missing final lemma.

Distinguished triangles and triangulated axioms over a trace doctrine.

A **boundary triangle** at a morphism `f : s → t` packages:
- `cone`  : a new object (the mapping cone)
- `incl`  : the inclusion `t → cone`
- `proj`  : the projection `cone → tate(1) ⊗ s`
- `exact` : the composition `proj ∘ incl ∘ f = 0`

The **triangulated axioms** (TR1--TR4) are recorded as exact theorem obligations
for cone data and shift data. No tautological surrogates are allowed.

The **DistinguishedTriangleData** packages a cone construction, shift data, and
the TR1--TR4 obligations.

The **RealizedBoundaryShadow** records the geometric boundary data (source and
target correspondences) extracted from a certified trace via realization.
-/

namespace MacLane.Trace

variable {D : TraceDoctrine}

/-! ## Distinguished triangles -/

/-- A distinguished triangle at `f : s → t` in a trace doctrine `D`.

    Packages:
    - `cone`  : the cone object
    - `incl`  : inclusion `t → cone`
    - `proj`  : projection `cone → tate ⊗ s`
    - `exact` : exactness `(f ∘ incl) ∘ proj = 0` -/
structure BoundaryTriangle {D : TraceDoctrine} {s t : D.Obj} (f : D.Hom s t) where
  cone  : D.Obj
  incl  : D.Hom t cone
  proj  : D.Hom cone (TraceDoctrine.tensor D (TraceDoctrine.tate D) s)
  exact : TraceDoctrine.comp D (TraceDoctrine.comp D f incl) proj = TraceDoctrine.zero_hom D

/-! ## Shift and triangle morphisms -/

/-- Suspension/shift data used in triangulated obligations. -/
structure TriangleShiftData (D : TraceDoctrine) where
  shiftHom : ∀ {X Y : D.Obj}, D.Hom X Y →
    D.Hom (TraceDoctrine.tensor D (TraceDoctrine.tate D) X)
          (TraceDoctrine.tensor D (TraceDoctrine.tate D) Y)

/-- A morphism between distinguished triangles over a commuting square. -/
structure TriangleMorphism
    {D : TraceDoctrine}
    (S : TriangleShiftData D)
    {s t s' t' : D.Obj}
    {f : D.Hom s t}
    {f' : D.Hom s' t'}
    (T : BoundaryTriangle (D := D) f)
    (T' : BoundaryTriangle (D := D) f')
    (a : D.Hom s s')
    (b : D.Hom t t') where
  coneMap : D.Hom T.cone T'.cone
  commute_source_target :
    TraceDoctrine.comp D f b = TraceDoctrine.comp D a f'
  commute_incl :
    TraceDoctrine.comp D T.incl coneMap = TraceDoctrine.comp D b T'.incl
  commute_proj :
    TraceDoctrine.comp D coneMap T'.proj =
      TraceDoctrine.comp D T.proj (S.shiftHom a)

/-! ## Triangulated axioms -/

/-- Triangulated obligations (TR1--TR4) for a fixed cone constructor and shift. -/
structure TriangulatedAxioms
    (D : TraceDoctrine)
    (tri : ∀ {s t : D.Obj} (f : D.Hom s t), BoundaryTriangle (D := D) f)
    (S : TriangleShiftData D) where
  /-- TR1: every morphism sits in its cone triangle (`tri f`), and exactness holds. -/
  tr1 : ∀ {s t : D.Obj} (f : D.Hom s t),
    TraceDoctrine.comp D (TraceDoctrine.comp D f (tri f).incl) (tri f).proj =
      TraceDoctrine.zero_hom D
  /-- TR2: rotation of a distinguished triangle is distinguished. -/
  tr2 : ∀ {s t : D.Obj} (f : D.Hom s t),
    Σ' (rot : BoundaryTriangle (D := D) (tri f).incl),
      TriangleMorphism S (tri f) rot f (tri f).incl
  /-- TR3: any commuting square extends to a morphism of distinguished triangles. -/
  tr3 : ∀ {s t s' t' : D.Obj}
      (f : D.Hom s t)
      (f' : D.Hom s' t')
      (a : D.Hom s s')
      (b : D.Hom t t')
      (hcomm : TraceDoctrine.comp D f b = TraceDoctrine.comp D a f'),
      Σ' (m : TriangleMorphism S (tri f) (tri f') a b),
        m.commute_source_target = hcomm
  /-- TR4 (octahedral): cone data for a composite factors through cone data of components. -/
  tr4 : ∀ {s t u : D.Obj}
      (f : D.Hom s t)
      (g : D.Hom t u),
      ∃ (k : D.Hom (tri f).cone (tri (TraceDoctrine.comp D f g)).cone)
        (l : D.Hom (tri (TraceDoctrine.comp D f g)).cone (tri g).cone),
        TraceDoctrine.comp D (tri f).incl k =
          TraceDoctrine.comp D g (tri (TraceDoctrine.comp D f g)).incl
        ∧ TraceDoctrine.comp D (tri (TraceDoctrine.comp D f g)).incl l = (tri g).incl
        ∧ TraceDoctrine.comp D l (tri g).proj =
          TraceDoctrine.comp D (tri (TraceDoctrine.comp D f g)).proj (S.shiftHom f)

/-! ## Distinguished triangle data -/

/-- `DistinguishedTriangleData` packages cone data, shift data, and TR1--TR4
    obligations for a trace doctrine. -/
structure DistinguishedTriangleData (D : TraceDoctrine) where
  /-- Cone construction for each morphism. -/
  triangle : ∀ {s t : D.Obj} (f : D.Hom s t), BoundaryTriangle (D := D) f
  /-- Shift/suspension data. -/
  shiftData : TriangleShiftData D
  /-- TR1--TR4 theorem obligations for this cone and shift data. -/
  axioms : TriangulatedAxioms D triangle shiftData

/-! ## Boundary codes -/

/-- The realized boundary shadow of a certified trace `T : s → t` at
    realization data `r, W`.

    This records the source and target correspondence data extracted from `T`
    by the realization functor `realizeCertifiedTrace r D`.  The boundary code
    is the "geometric boundary profile" of the trace — the data visible at
    the correspondence level. -/
structure RealizedBoundaryShadow
    {gens  : List Geometry.Schemes.SchemeOverQ}
    (r     : GeneratorRealization gens)
    (s t   : CanonicalWord gens) where
  /-- The correspondence realizing the source boundary. -/
  source_boundary : Geometry.Correspondences.ConcreteFiniteCorrespondence
    (realizeWord r s) (realizeWord r s)
  /-- The correspondence realizing the target boundary. -/
  target_boundary : Geometry.Correspondences.ConcreteFiniteCorrespondence
    (realizeWord r s) (realizeWord r t)

/-- Extract the realized boundary shadow from a certified trace via realization.

    The source boundary is the diagonal (identity) at `|s|`, and the target
    boundary is the realization of the trace `T` itself at `|t|`.
    (The boundary is "what is visible at source and target after applying T".) -/
noncomputable def CertifiedTrace.realizedBoundaryShadow
  {gens : List Geometry.Schemes.SchemeOverQ}
    (r    : GeneratorRealization gens)
    (W    : TcanData gens r)
    {s t  : CanonicalWord gens}
    (T    : CertifiedTrace gens s t) :
    RealizedBoundaryShadow r s t where
  source_boundary := W.diag s
  target_boundary := realizeCertifiedTrace r W T

end MacLane.Trace
