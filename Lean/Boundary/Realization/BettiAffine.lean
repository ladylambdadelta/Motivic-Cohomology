import Boundary.SmOver
import Boundary.Realization.AffineComplexPoints
import Boundary.Realization.AffineBettiChains

/-!
# Affine Betti realization API

This file exposes the affine-local Betti realization objects from
`AffineComplexPoints` under a stable public owner surface.
-/

noncomputable section

namespace Boundary
namespace Realization

/-- The canonical affine-open Betti chain presheaf. -/
noncomputable def canonicalSmAffineOpenBettiChainsPresheaf
    (X : Geometry.SmSchemeOver ℂ) :
    CategoryTheory.Functor (X.scheme.affineOpens) (ChainComplex (ModuleCat ℚ) ℕ) :=
  smAffineOpenCanonicalBettiChainsFunctor X

/-- The canonical affine Betti chain functor. -/
noncomputable def canonicalSmAffineBettiChainsFunctor :
    CategoryTheory.Functor (AffineSmOver ℂ) (ChainComplex (ModuleCat ℚ) ℕ) :=
  smAffineBettiChainsFunctor

end Realization
end Boundary
