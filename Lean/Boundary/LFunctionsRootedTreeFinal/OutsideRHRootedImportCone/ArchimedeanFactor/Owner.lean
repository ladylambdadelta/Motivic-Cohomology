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

theorem directSum_apply (a b : HodgeNumberProfile) (p q : ℤ) :
    directSum a b (p, q) = a (p, q) + b (p, q) :=
  rfl

theorem dual_apply (a : HodgeNumberProfile) (p q : ℤ) :
    dual a (p, q) = a (-p, -q) :=
  rfl

theorem tateTwist_apply (n : ℤ) (a : HodgeNumberProfile) (p q : ℤ) :
    tateTwist n a (p, q) = a (p + n, q + n) :=
  rfl

theorem dual_dual (a : HodgeNumberProfile) : dual (dual a) = a :=
  Hodge.BigradedRankProfile.dual_dual a

theorem tateTwist_zero (a : HodgeNumberProfile) : tateTwist 0 a = a :=
  Hodge.twistProfile_zero a

theorem directSum_comm (a b : HodgeNumberProfile) : directSum a b = directSum b a := by
  funext pq
  exact Nat.add_comm _ _

theorem directSum_assoc (a b c : HodgeNumberProfile) :
    directSum (directSum a b) c = directSum a (directSum b c) := by
  funext pq
  exact Nat.add_assoc _ _ _

theorem directSum_zero (a : HodgeNumberProfile) : directSum a 0 = a := by
  funext pq
  exact Nat.add_zero _

theorem zero_directSum (a : HodgeNumberProfile) : directSum 0 a = a := by
  funext pq
  exact zero_add _

theorem dual_directSum (a b : HodgeNumberProfile) :
    dual (directSum a b) = directSum (dual a) (dual b) := by
  funext pq
  rfl

theorem tateTwist_directSum (n : ℤ) (a b : HodgeNumberProfile) :
    tateTwist n (directSum a b) = directSum (tateTwist n a) (tateTwist n b) := by
  funext pq
  rfl

theorem dual_tateTwist (n : ℤ) (a : HodgeNumberProfile) :
    dual (tateTwist n a) = tateTwist (-n) (dual a) := by
  funext pq
  rcases pq with ⟨p, q⟩
  have hp : -p + n = -(p + -n) := by
    exact (Eq.trans (congrArg (fun t : ℤ => -p + t) (Eq.symm (neg_neg n)))
      (Eq.symm (neg_add p (-n))))
  have hq : -q + n = -(q + -n) := by
    exact (Eq.trans (congrArg (fun t : ℤ => -q + t) (Eq.symm (neg_neg n)))
      (Eq.symm (neg_add q (-n))))
  exact congrArg a (Prod.ext hp hq)

theorem tateTwist_dual (n : ℤ) (a : HodgeNumberProfile) :
    tateTwist n (dual a) = dual (tateTwist (-n) a) := by
  funext pq
  rcases pq with ⟨p, q⟩
  have hp : -(p + n) = -p + -n := by
    exact neg_add p n
  have hq : -(q + n) = -q + -n := by
    exact neg_add q n
  exact congrArg a (Prod.ext hp hq)

/-! ### Boundary-level profile transport

The archimedean packet route will eventually need to move between Hodge
structures and their rank profiles.  These lemmas make that transport explicit
at the Boundary layer instead of forcing later files to reopen the Hodge API.
-/

namespace Pure

open Boundary.Hodge

theorem rankProfile_tateTwist (H : PureHodgeStructure) (n : ℤ) :
    (H.tateTwist n).rankProfile = tateTwist n H.rankProfile := by
  exact Hodge.PureHodgeStructure.rankProfile_tateTwist H n

theorem rankProfile_product_add (H G : PureHodgeStructure) (hweight : H.weight = G.weight) :
    (H.product G hweight).rankProfile = directSum H.rankProfile G.rankProfile := by
  exact Hodge.PureHodgeStructure.rankProfile_product H G hweight

theorem rankProfile_ofLinearEquiv (H : PureHodgeStructure)
    {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (e : V ≃ₗ[ℚ] H.rationalCarrier) :
    (H.ofLinearEquiv e).rankProfile = H.rankProfile := by
  exact Hodge.PureHodgeStructure.rankProfile_ofLinearEquiv H e

theorem rankProfile_tateTwist_product (H G : PureHodgeStructure) (hweight : H.weight = G.weight)
    (n : ℤ) :
    ((H.product G hweight).tateTwist n).rankProfile =
      tateTwist n (directSum H.rankProfile G.rankProfile) := by
  calc
    ((H.product G hweight).tateTwist n).rankProfile =
        tateTwist n ((H.product G hweight).rankProfile) := by
      exact Hodge.PureHodgeStructure.rankProfile_tateTwist (H.product G hweight) n
    _ = tateTwist n (directSum H.rankProfile G.rankProfile) := by
      exact congrArg (tateTwist n) (Hodge.PureHodgeStructure.rankProfile_product H G hweight)

end Pure

end HodgeNumberProfile

end LFunctions
end Boundary
