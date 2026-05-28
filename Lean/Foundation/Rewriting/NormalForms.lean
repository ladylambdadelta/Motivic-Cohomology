/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:1752-1917 (localization and descent mechanisms using quotient/reduction behavior)
- our_paper_draft.tex:1926-2088 (effective presentation and stabilization, which require normal-form/quotient discipline)
- our_paper_draft.tex:2130-2166 (minimal-package soundness requiring rewrite admissibility discipline)
- our_paper_draft.tex:2501-2544 (comparison compatibility constraints that rely on rewriting invariants)
- our_paper_draft.tex:5700-5714 (pi0 comparison stage requiring quotient invariance)

Still missing in this file/module:
- Per-theorem manuscript labels attached to the exported rewriting API.
- Explicit statements of invariants needed by downstream motive and trace layers.
- Dependency exports in the exact signatures consumed by `Trace.NormalForm` and motive-comparison modules.

Coverage intent for this file:
- Keep implementation live and foundational.
- Treat this header as the temporary manuscript-proof coverage ledger for rewriting infrastructure.
-/

import Foundation.Rewriting.AbstractReduction
-- import Foundation.Rewriting.Termination  -- not yet used

/-!
# Normal Forms

This file defines normalizing interfaces over abstract reduction systems.
-/

universe u

namespace Foundation.Rewriting

namespace ReductionSystem

variable {α : Type u}

/-- Alias for readability: NormalFormData is the normal-form witness. -/
abbrev IsNormalForm (R : ReductionSystem α) (a : α) : Prop :=
  ∀ b : α, ¬ R.step a b

/-- Witness data that every element reduces to some normal form. -/
structure NormalizingData (R : ReductionSystem α) where
  /-- A canonical normal form selector. -/
  nf        : α → α
  /-- Each element reduces to its normal form. -/
  sound     : ∀ a : α, R.RedStar a (nf a)
  /-- The result is in normal form. -/
  nf_is_nf  : ∀ a : α, NormalFormData R (nf a)

/-- A concrete normal-form selector with soundness and completeness. -/
structure NormalizationFunction (R : ReductionSystem α) where
  nf : α → α
  sound : ∀ a : α, R.RedStar a (nf a)
  /-- The result is in normal form. -/
  nf_is_nf  : ∀ a : α, NormalFormData R (nf a)
  /-- Uniqueness: if `a →* b` and `b` is in NF, then `nf a = b`. -/
  complete  : ∀ a b : α, R.RedStar a b → NormalFormData R b → nf a = b

/-- Every normalization function gives a normalizing data. -/
def normalizingData_of_function (R : ReductionSystem α) (N : NormalizationFunction R) :
    NormalizingData R where
  nf       := N.nf
  sound    := N.sound
  nf_is_nf := N.nf_is_nf

/-- The normal-form selector is idempotent when uniqueness holds. -/
theorem nf_idempotent (R : ReductionSystem α) (N : NormalizationFunction R) (a : α) :
    N.nf (N.nf a) = N.nf a :=
  N.complete (N.nf a) (N.nf a) (redStar_refl R (N.nf a)) (N.nf_is_nf a)

end ReductionSystem

end Foundation.Rewriting
