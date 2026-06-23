import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroMultiplicityCore.RadialGap.Core.Owner

/-!
# Jensen radial-gap multiplicity core

This owner layer was split from `ZeroMultiplicityCore.RadialGap.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

/-- The origin-supported closed-disk summand is summable. -/
theorem entireFunctionOriginZeroMultiplicityClosedDiskSummable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    [Decidable (F 0 = 0)]
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [DecidableEq (EntireFunctionZero F)] :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) := by
  match (inferInstance : Decidable (F 0 = 0)) with
  | isTrue hF0 =>
    let z₀ : EntireFunctionZero F := ⟨0, hF0⟩
    have hsingle :
        Summable
          (fun z : EntireFunctionZero F =>
            if z = z₀ then
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
            else
              0) :=
      (hasSum_ite_eq z₀
        (entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀)).summable
    have hfun_eq :
        (fun z : EntireFunctionZero F =>
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z)
          =
        (fun z : EntireFunctionZero F =>
          if z = z₀ then
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
          else
            0) := by
      funext z
      exact
        (by
        change
          (if (z : ℂ) = 0 then
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
          else
            0) =
          (if z = z₀ then
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
          else
            0)
        match (inferInstance : Decidable (z = z₀)) with
        | isTrue hz =>
          have hz₀ : (z : ℂ) = 0 := by
            exact congrArg Subtype.val hz
          have horigin :
              (if (z : ℂ) = 0 then
                entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
              else
                0) = entireFunctionZeroMultiplicityClosedDiskSummand F hF R z :=
            if_pos hz₀
          have hclosed :
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z =
                entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀ := by
            exact congrArg
              (fun w : EntireFunctionZero F =>
                entireFunctionZeroMultiplicityClosedDiskSummand F hF R w) hz
          calc
            (if (z : ℂ) = 0 then
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
            else
              0) = entireFunctionZeroMultiplicityClosedDiskSummand F hF R z :=
                horigin
            _ = entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀ :=
                hclosed
            _ = (if z = z₀ then
                  entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
                else
                  0) := (if_pos hz).symm
        | isFalse hz =>
          have hz₀ : (z : ℂ) ≠ 0 := by
            intro hval
            exact hz (Subtype.ext hval)
          calc
            (if (z : ℂ) = 0 then
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
            else
              0) = 0 := if_neg hz₀
            _ = (if z = z₀ then
                  entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
                else
                  0) := (if_neg hz).symm)
    exact Eq.subst
      (motive := fun φ : EntireFunctionZero F → ℝ => Summable φ)
      hfun_eq.symm
      hsingle
  | isFalse hF0 =>
    have hzero :
        (fun z : EntireFunctionZero F =>
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z)
          =
        (fun _ : EntireFunctionZero F => 0) := by
      funext z
      change
        (if (z : ℂ) = 0 then
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
        else
          0) = 0
      have hz₀ : (z : ℂ) ≠ 0 := by
        intro hval
        have hzF : F 0 = 0 := by
          calc
            F 0 = F (z : ℂ) := congrArg F hval.symm
            _ = 0 := z.property
        exact hF0 hzF
      exact if_neg hz₀
    exact Eq.subst
      (motive := fun φ : EntireFunctionZero F → ℝ => Summable φ)
      hzero.symm
      summable_zero

/-- The origin multiplicity contribution used when the Jensen radial-gap sum is
written only over nonzero zeros. -/
noncomputable def entireFunctionOriginMultiplicityLogContribution
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z) : ℝ :=
  (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2

/-- The origin Taylor-factor contribution on the Jensen circle of radius `ρ`.

For `F(z)=z^m G(z)` near the origin, this term is `m log ρ` in the boundary
logarithmic average. -/
noncomputable def entireFunctionOriginMultiplicityLogRadiusContribution
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ) : ℝ :=
  (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log ρ

/-- A nonzero value at the origin has analytic multiplicity zero. -/
theorem entireFunctionZeroMultiplicity_origin_eq_zero_of_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    entireFunctionZeroMultiplicity F hF 0 = 0 := by
  have horder : (hF 0).order = (0 : ENat) := by
    exact
      ((hF 0).order_eq_nat_iff 0).mpr
        ⟨F, hF 0, hF0, Filter.Eventually.of_forall
          (fun w => by
            calc
              F w = 1 • F w := (one_smul ℂ (F w)).symm
              _ = (w - 0) ^ 0 • F w := by
                exact congrArg (fun a : ℂ => a • F w) (pow_zero (w - 0)).symm)⟩
  exact congrArg ENat.toNat horder

/-- The fixed origin Taylor contribution vanishes when `F 0 ≠ 0`. -/
theorem entireFunctionOriginMultiplicityLogContribution_eq_zero_of_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    entireFunctionOriginMultiplicityLogContribution F hF = 0 := by
  have hmult_zero :
      entireFunctionZeroMultiplicity F hF 0 = 0 :=
    entireFunctionZeroMultiplicity_origin_eq_zero_of_ne_zero F hF hF0
  calc
    (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2
        = (0 : ℝ) * Real.log 2 := by
          calc
            (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2
                = ((0 : ℕ) : ℝ) * Real.log 2 := by
                  exact congrArg (fun n : ℕ => (n : ℝ) * Real.log 2) hmult_zero
            _ = (0 : ℝ) * Real.log 2 := by
              exact congrArg (fun t : ℝ => t * Real.log 2) Nat.cast_zero
    _ = 0 := zero_mul (Real.log 2)

/-- The radius-dependent origin Taylor contribution vanishes when `F 0 ≠ 0`. -/
theorem entireFunctionOriginMultiplicityLogRadiusContribution_eq_zero_of_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ = 0 := by
  have hmult_zero :
      entireFunctionZeroMultiplicity F hF 0 = 0 :=
    entireFunctionZeroMultiplicity_origin_eq_zero_of_ne_zero F hF hF0
  calc
    (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log ρ
        = (0 : ℝ) * Real.log ρ := by
          calc
            (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log ρ
                = ((0 : ℕ) : ℝ) * Real.log ρ := by
                  exact congrArg (fun n : ℕ => (n : ℝ) * Real.log ρ) hmult_zero
            _ = (0 : ℝ) * Real.log ρ := by
              exact congrArg (fun t : ℝ => t * Real.log ρ) Nat.cast_zero
    _ = 0 := zero_mul (Real.log ρ)

/-- The origin-supported closed-disk summand is bounded by the fixed origin
Taylor contribution. -/
theorem entireFunctionOriginZeroMultiplicityClosedDisk_tsum_mul_log_two_le_originContribution
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    (hR : 1 ≤ R)
    [Decidable (F 0 = 0)] :
    (∑' z : EntireFunctionZero F,
        entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
        Real.log 2 ≤
      entireFunctionOriginMultiplicityLogContribution F hF := by
  match (inferInstance : Decidable (F 0 = 0)) with
  | isTrue hF0 =>
    let z₀ : EntireFunctionZero F := ⟨0, hF0⟩
    have horigin_eq :
        (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) =
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀ := by
      exact
        entireFunctionOriginZeroMultiplicityClosedDiskSummand_tsum_eq
          F hF (z₀ := z₀) rfl
    have hz₀_disk :
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀ =
          (entireFunctionZeroMultiplicity F hF 0 : ℝ) := by
      change
        (if ‖(z₀ : ℂ)‖ ≤ R then
          (entireFunctionZeroMultiplicity F hF (z₀ : ℂ) : ℝ)
        else
          0) =
        (entireFunctionZeroMultiplicity F hF 0 : ℝ)
      have hzero_le : ‖(z₀ : ℂ)‖ ≤ R := by
        calc
          ‖(z₀ : ℂ)‖ = ‖(0 : ℂ)‖ := by
            exact congrArg norm rfl
          _ = 0 := norm_zero
          _ ≤ 1 := zero_le_one
          _ ≤ R := hR
      exact if_pos hzero_le
    have hsum_eq :
        (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) =
          (entireFunctionZeroMultiplicity F hF 0 : ℝ) :=
      Eq.trans horigin_eq hz₀_disk
    have hprod_eq :
        (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
            Real.log 2 =
          (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2 := by
      exact congrArg (fun t : ℝ => t * Real.log 2) hsum_eq
    exact le_of_eq hprod_eq
  | isFalse hF0 =>
    have horigin_zero :
        (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) =
          0 := by
      have hzero :
          (fun z : EntireFunctionZero F =>
            entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z)
            =
          (fun _ : EntireFunctionZero F => 0) := by
        funext z
        change
          (if (z : ℂ) = 0 then
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
          else
            0) = 0
        have hz₀ : (z : ℂ) ≠ 0 := by
          intro hval
          have hzF : F 0 = 0 := by
            calc
              F 0 = F (z : ℂ) := congrArg F hval.symm
              _ = 0 := z.property
          exact hF0 hzF
        exact if_neg hz₀
      exact Eq.trans (tsum_congr (fun z => congrFun hzero z)) tsum_zero
    have hzero' :
        (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) =
          0 := horigin_zero
    have hleft_zero :
        (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
            Real.log 2 = 0 := by
      calc
        (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
            Real.log 2 = 0 * Real.log 2 := by
              exact congrArg (fun t : ℝ => t * Real.log 2) hzero'
        _ = 0 := zero_mul (Real.log 2)
    have hcontribution_zero :
        entireFunctionOriginMultiplicityLogContribution F hF = 0 :=
      entireFunctionOriginMultiplicityLogContribution_eq_zero_of_ne_zero F hF hF0
    exact le_of_eq (Eq.trans hleft_zero hcontribution_zero.symm)


end
end LFunctions
end Boundary
