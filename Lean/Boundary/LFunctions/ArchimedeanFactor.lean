import Boundary.Hodge.Tate

/-!
# Archimedean Hodge-number bookkeeping

This file records only the algebraic input to archimedean factors: Hodge-number
profiles and their behavior under sums, duals, and Tate twists.  Analytic
Gamma-factor identities are deliberately not introduced here.
-/

namespace Boundary
namespace LFunctions

abbrev HodgeNumberProfile := Hodge.BigradedRankProfile

namespace HodgeNumberProfile

/-- Direct-sum bookkeeping for Hodge-number profiles. -/
def directSum (a b : HodgeNumberProfile) : HodgeNumberProfile :=
  Hodge.BigradedRankProfile.add a b

/-- Dual bookkeeping for Hodge-number profiles. -/
def dual (a : HodgeNumberProfile) : HodgeNumberProfile :=
  Hodge.BigradedRankProfile.dual a

/-- Tate-twist bookkeeping for Hodge-number profiles. -/
def tateTwist (n : ℤ) (a : HodgeNumberProfile) : HodgeNumberProfile :=
  Hodge.twistProfile n a

@[simp]
theorem directSum_apply (a b : HodgeNumberProfile) (p q : ℤ) :
    directSum a b (p, q) = a (p, q) + b (p, q) :=
  rfl

@[simp]
theorem dual_apply (a : HodgeNumberProfile) (p q : ℤ) :
    dual a (p, q) = a (-p, -q) :=
  rfl

@[simp]
theorem tateTwist_apply (n : ℤ) (a : HodgeNumberProfile) (p q : ℤ) :
    tateTwist n a (p, q) = a (p + n, q + n) :=
  rfl

@[simp]
theorem dual_dual (a : HodgeNumberProfile) : dual (dual a) = a :=
  Hodge.BigradedRankProfile.dual_dual a

@[simp]
theorem tateTwist_zero (a : HodgeNumberProfile) : tateTwist 0 a = a :=
  Hodge.twistProfile_zero a

end HodgeNumberProfile

end LFunctions
end Boundary
