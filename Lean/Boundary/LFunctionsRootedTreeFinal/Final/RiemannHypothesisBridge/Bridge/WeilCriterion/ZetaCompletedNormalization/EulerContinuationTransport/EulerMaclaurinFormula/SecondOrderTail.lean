import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.SecondOrderBernoulli
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PostCutoffTail

/-!
# Second-order Euler--Maclaurin tail assembly

This layer specializes the zero-boundary Bernoulli block identity to the
complex-power tail and assembles consecutive unit blocks into one finite
interval identity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- Derivative of `x ↦ x^(-(z+1))` at a positive real point. -/
theorem eulerMaclaurin_cpow_neg_addOne_hasDerivAt
    (z : ℂ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-(z + 1))))
      (-(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2))))
      x := by
  have hslit : (x : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr hx
  have hcomplex :
      HasDerivAt
        (fun w : ℂ => w ^ (-(z + 1)))
        ((-(z + 1)) * ((x : ℂ) ^ ((-(z + 1)) - 1)) * 1)
        (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).cpow_const hslit
  have hreal :
      HasDerivAt
        (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-(z + 1))))
        ((-(z + 1)) * ((x : ℂ) ^ ((-(z + 1)) - 1)) * 1)
        x :=
    hcomplex.comp_ofReal
  have hexponent : (-(z + 1)) - 1 = -(z + 2) := by
    calc
      (-(z + 1)) - 1 = -(z + 1) + (-(1 : ℂ)) :=
        sub_eq_add_neg (-(z + 1)) 1
      _ = -((z + 1) + 1) := (neg_add (z + 1) 1).symm
      _ = -(z + (1 + 1)) :=
        congrArg Neg.neg (add_assoc z 1 1)
      _ = -(z + 2) :=
        congrArg (fun value : ℂ => -(z + value))
          (one_add_one_eq_two : (1 : ℂ) + 1 = 2)
  have hcoefficient :
      ((-(z + 1)) * ((x : ℂ) ^ ((-(z + 1)) - 1)) * 1) =
        -(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2))) := by
    calc
      ((-(z + 1)) * ((x : ℂ) ^ ((-(z + 1)) - 1)) * 1) =
          (-(z + 1)) * ((x : ℂ) ^ ((-(z + 1)) - 1)) :=
        mul_one _
      _ = -(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2))) :=
        congrArg (fun value : ℂ => -(z + 1) * value)
          (congrArg (fun exponent : ℂ => (x : ℂ) ^ exponent) hexponent)
  exact hreal.congr_deriv hcoefficient

/-- The complex-power phase and its derivative are interval integrable on a
positive natural unit block. -/
theorem eulerMaclaurin_cpow_neg_addOne_unitBlock_intervalIntegrable
    (z : ℂ)
    (n : ℕ)
    (hn : 0 < n) :
    IntervalIntegrable
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
        volume
        (n : ℝ)
        ((n : ℝ) + 1) ∧
      IntervalIntegrable
        (fun x : ℝ =>
          -(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2))))
        volume
        (n : ℝ)
        ((n : ℝ) + 1) := by
  have hphaseContinuous :
      ContinuousOn
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
        (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
    intro x hx
    have hxPositive : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn) hx.1
    exact
      (Complex.continuousAt_ofReal_cpow_const x (-(z + 1))
        (Or.inr (ne_of_gt hxPositive))).continuousWithinAt
  have hderivativeContinuous :
      ContinuousOn
        (fun x : ℝ =>
          -(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2))))
        (Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
    intro x hx
    have hxPositive : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn) hx.1
    have hcpow :
        ContinuousAt (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-(z + 2)))) x :=
      Complex.continuousAt_ofReal_cpow_const x (-(z + 2))
        (Or.inr (ne_of_gt hxPositive))
    exact (continuousAt_const.mul hcpow).continuousWithinAt
  have hblockOrder : (n : ℝ) ≤ (n : ℝ) + 1 :=
    le_add_of_nonneg_right zero_le_one
  have hphaseContinuousUnordered :
      ContinuousOn
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
        (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) :=
    Eq.subst
      (motive := fun interval : Set ℝ =>
        ContinuousOn
          (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
          interval)
      (Set.uIcc_of_le hblockOrder).symm
      hphaseContinuous
  have hderivativeContinuousUnordered :
      ContinuousOn
        (fun x : ℝ =>
          -(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2))))
        (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) :=
    Eq.subst
      (motive := fun interval : Set ℝ =>
        ContinuousOn
          (fun x : ℝ =>
            -(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2))))
          interval)
      (Set.uIcc_of_le hblockOrder).symm
      hderivativeContinuous
  exact
    ⟨hphaseContinuousUnordered.intervalIntegrable,
      hderivativeContinuousUnordered.intervalIntegrable⟩

/-- Second integration by parts for the zeta Bernoulli remainder on one
positive natural unit block. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_cpow_secondOrder_oneBlock
    (z : ℂ)
    (n : ℕ)
    (hn : 0 < n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1),
        (((x : ℝ) : ℂ) ^ (-(z + 1))) *
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)) =
      -∫ x in (n : ℝ)..((n : ℝ) + 1),
        (-(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2)))) *
          eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x := by
  have hintegrable :=
    eulerMaclaurin_cpow_neg_addOne_unitBlock_intervalIntegrable z n hn
  exact eulerMaclaurin_firstPeriodicBernoulli_secondOrder_oneBlock
    (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
    (fun x : ℝ => -(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2))))
    n
    (fun x hx =>
      have hblockOrder : (n : ℝ) ≤ (n : ℝ) + 1 :=
        le_add_of_nonneg_right zero_le_one
      have hxOrdered : x ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) :=
        Eq.subst
          (motive := fun interval : Set ℝ => x ∈ interval)
          (Set.uIcc_of_le hblockOrder)
          hx
      have hxLower : (n : ℝ) ≤ x := hxOrdered.1
      have hxPositive : 0 < x :=
        lt_of_lt_of_le (Nat.cast_pos.mpr hn) hxLower
      eulerMaclaurin_cpow_neg_addOne_hasDerivAt z hxPositive)
    hintegrable.2

/-- Finite consecutive-block form of the second-order Bernoulli identity. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_cpow_secondOrder_finiteTail
    (z : ℂ)
    (N M : ℕ)
    (hN : 0 < N)
    (hNM : N ≤ M) :
    (∫ x in (N : ℝ)..(M : ℝ),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(z + 1)))) =
      -∑ n ∈ Finset.Ico N M,
        ∫ x in (n : ℝ)..((n : ℝ) + 1),
          (-(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2)))) *
            eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x := by
  let phase : ℝ → ℂ :=
    fun x : ℝ => ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have hblockIntegrable :
      ∀ n ∈ Set.Ico N M,
        IntervalIntegrable phase volume (n : ℝ) (((n + 1 : ℕ) : ℝ)) := by
    intro n hnMembership
    have hnNat : N ≤ n := hnMembership.1
    have hnPositive : 0 < n := lt_of_lt_of_le hN hnNat
    have hcpowIntegrable :=
      (eulerMaclaurin_cpow_neg_addOne_unitBlock_intervalIntegrable z n hnPositive).1
    have hcpowSetIntegrable :
        IntegrableOn
          (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
          (Set.Ioc (n : ℝ) ((n : ℝ) + 1)) :=
      hcpowIntegrable.1
    have hproductSetIntegrable :
        IntegrableOn phase (Set.Ioc (n : ℝ) ((n : ℝ) + 1)) :=
      eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
        (n : ℝ)
        ((n : ℝ) + 1)
        hcpowSetIntegrable
    have hproduct :
        IntervalIntegrable phase volume (n : ℝ) ((n : ℝ) + 1) :=
      ⟨hproductSetIntegrable,
        hproductSetIntegrable.mono_set
          (fun x hx =>
            False.elim
              (not_lt_of_ge
                (le_trans hx.2 (le_add_of_nonneg_right zero_le_one))
                hx.1))⟩
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 :=
      Nat.cast_add_one n
    exact Eq.subst
      (motive := fun upper : ℝ =>
        IntervalIntegrable phase volume (n : ℝ) upper)
      hcast.symm
      hproduct
  have hleftSum :
      (∑ n ∈ Finset.Ico N M,
        ∫ x in (n : ℝ)..(((n + 1 : ℕ) : ℝ)), phase x) =
        ∫ x in (N : ℝ)..(M : ℝ), phase x :=
    intervalIntegral.sum_integral_adjacent_intervals_Ico
      hNM hblockIntegrable
  have hblockIdentity :
      ∀ n ∈ Finset.Ico N M,
        (∫ x in (n : ℝ)..(((n + 1 : ℕ) : ℝ)), phase x) =
          -∫ x in (n : ℝ)..((n : ℝ) + 1),
            (-(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2)))) *
              eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x := by
    intro n hnMembership
    have hnNat : N ≤ n := (Finset.mem_Ico.mp hnMembership).1
    have hnPositive : 0 < n := lt_of_lt_of_le hN hnNat
    have hraw :=
      eulerMaclaurin_firstPeriodicBernoulli_cpow_secondOrder_oneBlock
        z n hnPositive
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 :=
      Nat.cast_add_one n
    have hcommuted :
        (∫ x in (n : ℝ)..((n : ℝ) + 1), phase x) =
          ∫ x in (n : ℝ)..((n : ℝ) + 1),
            (((x : ℝ) : ℂ) ^ (-(z + 1))) *
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) := by
      exact intervalIntegral.integral_congr
        (fun x _hx =>
          mul_comm
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
            (((x : ℝ) : ℂ) ^ (-(z + 1))))
    have hphaseRaw := Eq.trans hcommuted hraw
    exact Eq.subst
      (motive := fun upper : ℝ =>
        (∫ x in (n : ℝ)..upper, phase x) =
          -∫ x in (n : ℝ)..((n : ℝ) + 1),
            (-(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2)))) *
              eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x)
      hcast.symm
      hphaseRaw
  have hsumIdentity :
      (∑ n ∈ Finset.Ico N M,
        ∫ x in (n : ℝ)..(((n + 1 : ℕ) : ℝ)), phase x) =
        ∑ n ∈ Finset.Ico N M,
          -∫ x in (n : ℝ)..((n : ℝ) + 1),
            (-(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2)))) *
              eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x :=
    Finset.sum_congr rfl hblockIdentity
  have hnegativeSum :
      (∑ n ∈ Finset.Ico N M,
          -∫ x in (n : ℝ)..((n : ℝ) + 1),
            (-(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2)))) *
              eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x) =
        -∑ n ∈ Finset.Ico N M,
          ∫ x in (n : ℝ)..((n : ℝ) + 1),
            (-(z + 1) * (((x : ℝ) : ℂ) ^ (-(z + 2)))) *
              eulerMaclaurinSecondOrderBernoulliBlockPrimitive n x :=
    Finset.sum_neg_distrib
  exact Eq.trans hleftSum.symm (Eq.trans hsumIdentity hnegativeSum)

end
end LFunctions
end Boundary
