import Boundary.OpenClosedLocalization

/-!
# Tate Stabilization Target Surface

This file records the exact source-side theorem surface for Tate/`P1`
stabilization above the minimal presentation package.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

noncomputable section

/-- Exact theorem-target package for Tate stabilization relative to a minimal
presentation package.  It mirrors the manuscript split between the Tate object,
the `P1` model, and compatibility with localization. -/
structure TateStabilizationPresentationQ
    (category : SmCorQ (k := k))
    (package : MinimalPresentationPackageQ category) where
  TateWitness : Type (u + 1)
  tateGenerator : TateWitness → package.GeneratorIndex
  p1Generator : TateWitness → package.GeneratorIndex
  stabilizeWithTate : TateWitness → package.GeneratorIndex → package.GeneratorIndex
  stabilizeWithP1 : TateWitness → package.GeneratorIndex → package.GeneratorIndex
  tateObjectTarget : ∀ witness : TateWitness, Prop
  p1ObjectTarget : ∀ witness : TateWitness, Prop
  stabilizationComparisonTarget :
    ∀ witness : TateWitness,
      ∀ idx : package.GeneratorIndex,
        Prop
  localizationRespectsStabilizationTarget : Prop

namespace TateStabilizationPresentationQ

def theoremTarget
    {category : SmCorQ (k := k)}
    {package : MinimalPresentationPackageQ category}
    (presentation : TateStabilizationPresentationQ category package) : Prop :=
  (∀ witness : presentation.TateWitness,
      ∀ idx : package.GeneratorIndex,
        presentation.stabilizationComparisonTarget witness idx) ∧
    presentation.localizationRespectsStabilizationTarget

end TateStabilizationPresentationQ

/-- Certified wrapper for the Tate stabilization theorem surface. -/
structure CertifiedTateStabilizationPresentationQ
    (category : SmCorQ (k := k))
    (package : MinimalPresentationPackageQ category) where
  target : TateStabilizationPresentationQ category package
  theorem_holds : target.theoremTarget

end

end Boundary
