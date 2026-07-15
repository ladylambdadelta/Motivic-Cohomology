import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.ConstantTermAssembly

/-!
# Reindexing consecutive natural-number blocks
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A sum over the consecutive block endpoints `(C, C + D]` is the sum over
the zero-based block offsets of length `D`. -/
theorem sum_Ioc_add_eq_sum_range_add_succ
    {A : Type*}
    [AddCommMonoid A]
    (f : ℕ → A)
    (C D : ℕ) :
    (∑ n ∈ Finset.Ioc C (C + D), f n) =
      ∑ k ∈ Finset.range D, f (C + k + 1) := by
  induction D with
  | zero =>
      have hupper : C + 0 = C :=
        Nat.add_zero C
      have hleft : Finset.Ioc C (C + 0) = ∅ :=
        Eq.trans
          (congrArg (fun upper : ℕ => Finset.Ioc C upper) hupper)
          (Finset.Ioc_self C)
      have hright : Finset.range 0 = ∅ :=
        Finset.range_zero
      exact Eq.trans
        (congrArg (fun s : Finset ℕ => ∑ n ∈ s, f n) hleft)
        (Eq.trans
          (Finset.sum_empty)
          (Eq.trans
            (Finset.sum_empty).symm
            (congrArg
              (fun s : Finset ℕ => ∑ k ∈ s, f (C + k + 1))
              hright.symm)))
  | succ D ih =>
      have hC_le : C ≤ C + D :=
        Nat.le_add_right C D
      have hleftStep :
          (∑ n ∈ Finset.Ioc C (C + (D + 1)), f n) =
            (∑ n ∈ Finset.Ioc C (C + D), f n) + f (C + D + 1) := by
        have hupper : C + (D + 1) = (C + D) + 1 :=
          (Nat.add_assoc C D 1).symm
        exact Eq.trans
          (congrArg
            (fun upper : ℕ => ∑ n ∈ Finset.Ioc C upper, f n)
            hupper)
          (Finset.sum_Ioc_succ_top hC_le f)
      have hrightStep :
          (∑ k ∈ Finset.range (D + 1), f (C + k + 1)) =
            (∑ k ∈ Finset.range D, f (C + k + 1)) + f (C + D + 1) :=
        Finset.sum_range_succ (fun k : ℕ => f (C + k + 1)) D
      exact Eq.trans hleftStep
        (Eq.trans
          (congrArg (fun z : A => z + f (C + D + 1)) ih)
          hrightStep.symm)

end
end LFunctions
end Boundary
