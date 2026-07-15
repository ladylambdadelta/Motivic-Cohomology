import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part05_NormalizedKernelLocal
import Mathlib.MeasureTheory.Integral.Bochner

/-!
# Boundary growth owner part 6

This file is a mechanical forward-order split of `BoundaryGrowth.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory
local notation "π" => Real.pi

/-- The reciprocal-drift unit contribution and one sharp phase contribution
fit inside the existing `2 * sqrt (1 + |t|) * log (2 + M)` block scale. -/
theorem boundaryLineOnePointRealParam_one_add_sqrt_log_le_two_sqrt_log_postCutoff
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (1 : ℝ) + Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let A : ℝ := Real.sqrt (1 + ‖t‖) * Real.log (2 + M)
  have hone_le_A : (1 : ℝ) ≤ A :=
    boundaryLineOnePointRealParam_one_le_sqrt_one_add_norm_mul_log_two_add_postCutoff
      t ht hM
  have hsum : (1 : ℝ) + A ≤ A + A :=
    add_le_add_right hone_le_A A
  have htwo : A + A = 2 * A :=
    (two_mul A).symm
  have htwoTarget :
      A + A = 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    Eq.trans htwo
      (mul_assoc (2 : ℝ) (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm
  exact Eq.subst
    (motive := fun r : ℝ => (1 : ℝ) + A ≤ r)
    htwoTarget
    hsum

/-- Pointwise algebraic split of the local normalized-kernel defect into
reciprocal drift and phase drift.

This is the reusable owner-level algebra behind the finite block cancellation:
it separates the exact defect before any norm or scalar majorant is taken. -/
theorem boundaryLineOnePointRealParam_normalizedKernel_defect_eq_reciprocal_add_phase_pointwise
    (t : ℝ)
    (x : ℝ)
    (y : ℂ) :
    (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (((-(t : ℂ) * Complex.I) / y) *
        (y ^ (-(t : ℂ) * Complex.I)))) =
      (-(t : ℂ) * Complex.I) *
        ((((x : ℂ)⁻¹ - y⁻¹) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          y⁻¹ *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              (y ^ (-(t : ℂ) * Complex.I)))) := by
  let A : ℂ := -(t : ℂ) * Complex.I
  let P : ℂ := (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let Q : ℂ := y ^ (-(t : ℂ) * Complex.I)
  have hx_div : (-(t : ℂ) * Complex.I) / (x : ℂ) = A * (x : ℂ)⁻¹ :=
    div_eq_mul_inv A (x : ℂ)
  have hy_div : (-(t : ℂ) * Complex.I) / y = A * y⁻¹ :=
    div_eq_mul_inv A y
  have hinner :
      ((x : ℂ)⁻¹ * P) - (y⁻¹ * Q) =
        (((x : ℂ)⁻¹ - y⁻¹) * P) + y⁻¹ * (P - Q) := by
    calc
      ((x : ℂ)⁻¹ * P) - (y⁻¹ * Q) =
          (((x : ℂ)⁻¹ * P) - (y⁻¹ * P)) +
            ((y⁻¹ * P) - (y⁻¹ * Q)) := by
        have hcancel :
            (((x : ℂ)⁻¹ * P) - (y⁻¹ * P)) +
                ((y⁻¹ * P) - (y⁻¹ * Q)) =
              ((x : ℂ)⁻¹ * P) - (y⁻¹ * Q) := by
          calc
            (((x : ℂ)⁻¹ * P) - (y⁻¹ * P)) +
                ((y⁻¹ * P) - (y⁻¹ * Q)) =
                (((x : ℂ)⁻¹ * P) + -(y⁻¹ * P)) +
                  ((y⁻¹ * P) + -(y⁻¹ * Q)) := by
              exact congrArg₂ Add.add
                (sub_eq_add_neg ((x : ℂ)⁻¹ * P) (y⁻¹ * P))
                (sub_eq_add_neg (y⁻¹ * P) (y⁻¹ * Q))
            _ = ((x : ℂ)⁻¹ * P) +
                  (-(y⁻¹ * P) + ((y⁻¹ * P) + -(y⁻¹ * Q))) := by
              exact add_assoc (((x : ℂ)⁻¹ * P)) (-(y⁻¹ * P))
                ((y⁻¹ * P) + -(y⁻¹ * Q))
            _ = ((x : ℂ)⁻¹ * P) +
                  ((-(y⁻¹ * P) + (y⁻¹ * P)) + -(y⁻¹ * Q)) := by
              exact congrArg
                (fun z : ℂ => ((x : ℂ)⁻¹ * P) + z)
                (add_assoc (-(y⁻¹ * P)) (y⁻¹ * P) (-(y⁻¹ * Q))).symm
            _ = ((x : ℂ)⁻¹ * P) + (0 + -(y⁻¹ * Q)) := by
              exact congrArg
                (fun z : ℂ => ((x : ℂ)⁻¹ * P) + (z + -(y⁻¹ * Q)))
                (neg_add_cancel (y⁻¹ * P))
            _ = ((x : ℂ)⁻¹ * P) + -(y⁻¹ * Q) := by
              exact congrArg
                (fun z : ℂ => ((x : ℂ)⁻¹ * P) + z)
                (zero_add (-(y⁻¹ * Q)))
            _ = ((x : ℂ)⁻¹ * P) - (y⁻¹ * Q) := by
              exact (sub_eq_add_neg ((x : ℂ)⁻¹ * P) (y⁻¹ * Q)).symm
        exact hcancel.symm
      _ = (((x : ℂ)⁻¹ - y⁻¹) * P) + ((y⁻¹ * P) - (y⁻¹ * Q)) := by
        exact congrArg (fun z : ℂ => z + ((y⁻¹ * P) - (y⁻¹ * Q)))
          (sub_mul ((x : ℂ)⁻¹) y⁻¹ P).symm
      _ = (((x : ℂ)⁻¹ - y⁻¹) * P) + y⁻¹ * (P - Q) := by
        exact congrArg
          (fun z : ℂ => (((x : ℂ)⁻¹ - y⁻¹) * P) + z)
          (mul_sub y⁻¹ P Q).symm
  calc
    (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (((-(t : ℂ) * Complex.I) / y) *
        (y ^ (-(t : ℂ) * Complex.I)))) =
        (A * (x : ℂ)⁻¹) * P - (A * y⁻¹) * Q := by
      exact congrArg₂ Sub.sub
        (congrArg (fun z : ℂ => z * P) hx_div)
        (congrArg (fun z : ℂ => z * Q) hy_div)
    _ = A * (((x : ℂ)⁻¹ * P) - (y⁻¹ * Q)) := by
      have hleftAssociation :
          (A * (x : ℂ)⁻¹) * P = A * ((x : ℂ)⁻¹ * P) :=
        mul_assoc A (x : ℂ)⁻¹ P
      have hrightAssociation :
          (A * y⁻¹) * Q = A * (y⁻¹ * Q) :=
        mul_assoc A y⁻¹ Q
      have hassociatedDifference :
          (A * (x : ℂ)⁻¹) * P - (A * y⁻¹) * Q =
            A * ((x : ℂ)⁻¹ * P) - A * (y⁻¹ * Q) :=
        congrArg₂ Sub.sub hleftAssociation hrightAssociation
      exact Eq.trans hassociatedDifference
        (mul_sub A ((x : ℂ)⁻¹ * P) (y⁻¹ * Q)).symm
    _ = A * ((((x : ℂ)⁻¹ - y⁻¹) * P) + y⁻¹ * (P - Q)) := by
      exact congrArg (fun z : ℂ => A * z) hinner
    _ = (-(t : ℂ) * Complex.I) *
        ((((x : ℂ)⁻¹ - y⁻¹) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          y⁻¹ *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              (y ^ (-(t : ℂ) * Complex.I)))) := rfl

/-- Exact finite algebraic split of the oscillatory Bernoulli block sum into
reciprocal-drift and phase-drift pieces inside each local block.

This is the first Dirichlet/Abel block decomposition before taking norms: the
oscillatory factors remain inside the finite sum, so no cancellation has
been discarded into the scalar movement envelope. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_finiteOscillatoryBlockSum_eq_reciprocal_add_phaseBlocks
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I)))))))) := by
  let A : ℂ := -(t : ℂ) * Complex.I
  have hlocal :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) * (
                (((x : ℂ)⁻¹ -
                    (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                    ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                        (-(t : ℂ) * Complex.I))))))))) := by
    intro n hnMembership
    let y : ℂ := (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)
    let s : Set ℝ :=
      Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))
    let B : ℝ → ℂ := fun x =>
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
    let P : ℝ → ℂ := fun x =>
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
    let Py : ℂ := y ^ (-(t : ℂ) * Complex.I)
    have hpoint :
        (fun x : ℝ =>
          B x *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                P x) -
              (((-(t : ℂ) * Complex.I) / y) * Py)))) =
          (fun x : ℝ =>
            B x *
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ - y⁻¹) * P x +
                  y⁻¹ * (P x - Py)))) := by
      funext x
      exact congrArg
        (fun kernelValue : ℂ => B x * kernelValue)
        (boundaryLineOnePointRealParam_normalizedKernel_defect_eq_reciprocal_add_phase_pointwise
          t x y)
    exact congrArg (fun integrand : ℝ → ℂ => ∫ x in s, integrand x) hpoint
  have hsum :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))))) =
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ -
                    (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                    ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                        (-(t : ℂ) * Complex.I)))))))) := by
    exact Finset.sum_congr rfl hlocal
  exact hsum

/-- Pointwise distribution of the already-split normalized-kernel block into
the reciprocal-drift and phase-drift summands.

This is the algebraic local sink needed before the finite block sum can be
estimated by the reciprocal telescope plus the sharp Bernoulli phase
cancellation. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_splitBlock_integrand_eq_reciprocal_add_phaseDrift
    (t : ℝ)
    (n : ℕ)
    (x : ℝ) :
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          (((x : ℂ)⁻¹ -
              (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) +
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))) := by
  let B : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let A : ℂ := -(t : ℂ) * Complex.I
  let R : ℂ :=
    (((x : ℂ)⁻¹ -
        (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  let P : ℂ :=
    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
      ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I)))))
  calc
    B * (A * (R + P)) = B * (A * R + A * P) := by
      exact congrArg (fun z : ℂ => B * z) (mul_add A R P)
    _ = B * (A * R) + B * (A * P) := by
      exact mul_add B (A * R) (A * P)
    _ =
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) +
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))) := rfl

/-- Local integral-level distribution of one split normalized-kernel block.

The only hypotheses are the concrete local integrability facts needed for
Bochner linearity of the reciprocal-drift and phase-drift summands. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_splitBlock_integral_eq_reciprocal_add_phaseDrift
    (t : ℝ)
    (n : ℕ)
    (hrecip :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))
        (volume.restrict
          (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))))
    (hphase :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))))
        (volume.restrict
          (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))))) :
    (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          (((x : ℂ)⁻¹ -
              (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))) +
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))))) := by
  have hpoint :
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))))) =
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) +
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I))))))) := by
    funext x
    exact
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_splitBlock_integrand_eq_reciprocal_add_phaseDrift
        t n x
  have hintegral :
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))))) =
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) +
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                ((-(t : ℂ) * Complex.I) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                    ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I))))))) := by
    exact congrArg
      (fun f : ℝ → ℂ =>
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x)
      hpoint
  exact Eq.trans hintegral
    (MeasureTheory.integral_add hrecip hphase)

/-- Local integrability of the reciprocal-drift summand in one selected
post-cutoff Bernoulli block. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDrift_integrable
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    Integrable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  have hC_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hC_lt_n
  have hn_pred_pos : 0 < n - 1 :=
    Nat.sub_pos_of_lt hone_lt_n
  have hle :
      ((((n - 1 : ℕ) : ℕ) : ℝ)) ≤ (((n : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.sub_le n 1)
  have hcont_cpow :
      ContinuousOn
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn_pred_pos) hx.1
    exact
      (Complex.continuousAt_ofReal_cpow_const x (-(t : ℂ) * Complex.I)
        (Or.inr (ne_of_gt hx_pos))).continuousWithinAt
  have hcont_inv :
      ContinuousOn
        (fun x : ℝ => (x : ℂ)⁻¹)
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn_pred_pos) hx.1
    exact
      (Complex.continuous_ofReal.continuousAt.inv₀
        (Complex.ofReal_ne_zero.mpr (ne_of_gt hx_pos))).continuousWithinAt
  have hcont_recip :
      ContinuousOn
        (fun x : ℝ =>
          (x : ℂ)⁻¹ -
            (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) :=
    hcont_inv.sub continuousOn_const
  have hcont_kernel :
      ContinuousOn
        (fun x : ℝ =>
          (-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) :=
    continuousOn_const.mul (hcont_recip.mul hcont_cpow)
  have hkernel :
      IntegrableOn
        (fun x : ℝ =>
          (-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (ContinuousOn.intervalIntegrable_of_Icc hle hcont_kernel)
  exact
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun x : ℝ =>
        (-(t : ℂ) * Complex.I) *
          (((x : ℂ)⁻¹ -
              (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
      ((((n - 1 : ℕ) : ℕ) : ℝ))
      (((n : ℕ) : ℝ))
      hkernel

/-- Local integrability of the phase-drift summand in one selected
post-cutoff Bernoulli block. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDrift_integrable
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    Integrable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  have hC_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hC_lt_n
  have hn_pred_pos : 0 < n - 1 :=
    Nat.sub_pos_of_lt hone_lt_n
  have hle :
      ((((n - 1 : ℕ) : ℕ) : ℝ)) ≤ (((n : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.sub_le n 1)
  have hcont_cpow :
      ContinuousOn
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn_pred_pos) hx.1
    exact
      (Complex.continuousAt_ofReal_cpow_const x (-(t : ℂ) * Complex.I)
        (Or.inr (ne_of_gt hx_pos))).continuousWithinAt
  have hcont_increment :
      ContinuousOn
        (fun x : ℝ =>
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) :=
    hcont_cpow.sub continuousOn_const
  have hcont_weighted :
      ContinuousOn
        (fun x : ℝ =>
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) :=
    continuousOn_const.mul hcont_increment
  have hcont_kernel :
      ContinuousOn
        (fun x : ℝ =>
          (-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) :=
    continuousOn_const.mul hcont_weighted
  have hkernel :
      IntegrableOn
        (fun x : ℝ =>
          (-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (ContinuousOn.intervalIntegrable_of_Icc hle hcont_kernel)
  exact
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun x : ℝ =>
        (-(t : ℂ) * Complex.I) *
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))))
      ((((n - 1 : ℕ) : ℕ) : ℝ))
      (((n : ℕ) : ℝ))
      hkernel

/-- Exact finite split of the normalized Bernoulli oscillatory block sum into
the reciprocal-drift sum and the phase-drift sum. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_finiteOscillatoryBlockSum_eq_reciprocalDrift_add_phaseDrift
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))) +
        (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I))))))) := by
  have hsplitInside :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))) =
        (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) * (
                (((x : ℂ)⁻¹ -
                    (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                    ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                        (-(t : ℂ) * Complex.I)))))))) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_finiteOscillatoryBlockSum_eq_reciprocal_add_phaseBlocks
      t
  have hlocal :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) * (
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I))))))))) =
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ -
                    (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))) +
            (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                ((-(t : ℂ) * Complex.I) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                    ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                        (-(t : ℂ) * Complex.I))))))) := by
    intro n hn
    exact
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_splitBlock_integral_eq_reciprocal_add_phaseDrift
        t n
        (boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDrift_integrable
          t hn)
        (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDrift_integrable
          t hn)
  have hsum :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) * (
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I))))))))) =
        (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ -
                    (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))) +
          (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                ((-(t : ℂ) * Complex.I) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                    ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                        (-(t : ℂ) * Complex.I))))))) := by
    exact Eq.trans
      (Finset.sum_congr rfl hlocal)
      (Finset.sum_add_distrib)
  exact Eq.trans hsplitInside hsum

/-- Pointwise reciprocal-drift bound on a selected right-endpoint block.

This is the local analytic input for the reciprocal-variation half of the
normalized Bernoulli block cancellation.  The oscillatory factor has unit norm,
the first periodic Bernoulli factor is bounded by one, and the reciprocal
movement is controlled by the square of the left endpoint. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDrift_pointwise_norm_le
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M)
    {x : ℝ}
    (hx : x ∈ Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) :
    ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          (((x : ℂ)⁻¹ -
              (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
      ‖t‖ *
        ((1 : ℝ) /
          (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ)))) := by
  let m : ℕ := n - 1
  let mr : ℝ := ((m : ℕ) : ℝ)
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hcutoff_lt_n
  have hm_pos : 0 < m :=
    Nat.sub_pos_of_lt hone_lt_n
  have hn_eq : m + 1 = n :=
    Nat.sub_add_cancel (lt_trans hcutoff_pos hcutoff_lt_n)
  have hx_m :
      x ∈ Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)) := by
    exact Eq.subst
      (motive := fun q : ℕ =>
        x ∈ Set.Ioc (((m : ℕ) : ℝ)) (((q : ℕ) : ℝ)))
      hn_eq.symm
      hx
  have hB :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ (1 : ℝ) :=
    eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x
  have ha :
      ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hrecip :
      ‖(x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹‖ ≤
        (1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ)) :=
    boundaryLineOnePointRealParam_oneInterval_reciprocal_movement_norm_le
      hm_pos hx_m
  have hx_pos : 0 < x :=
    lt_trans (Nat.cast_pos.mpr hm_pos) hx_m.1
  have hphase :
      ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ = (1 : ℝ) :=
    boundaryLineOnePointRealParam_logarithmicPhase_cpow_norm_eq_one_of_pos
      t hx_pos
  have hraw :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((m : ℕ) : ℝ) : ℂ)⁻¹) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
        ‖t‖ *
          ((1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ))) := by
    calc
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((m : ℕ) : ℝ) : ℂ)⁻¹) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ =
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
            ‖(-(t : ℂ) * Complex.I)‖ *
              ‖((x : ℂ)⁻¹ -
                  (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ := by
        calc
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ -
                    (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖(-(t : ℂ) * Complex.I) *
                  (((x : ℂ)⁻¹ -
                      (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ := by
            exact norm_mul
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ -
                    (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
          _ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                (‖(-(t : ℂ) * Complex.I)‖ *
                  ‖((x : ℂ)⁻¹ -
                      (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖) := by
            exact congrArg
              (fun r : ℝ =>
                ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ * r)
              (norm_mul (-(t : ℂ) * Complex.I)
                (((x : ℂ)⁻¹ -
                    (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
          _ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖(-(t : ℂ) * Complex.I)‖ *
                  ‖((x : ℂ)⁻¹ -
                      (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ := by
            exact (mul_assoc
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖
              ‖(-(t : ℂ) * Complex.I)‖
              ‖((x : ℂ)⁻¹ -
                  (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖).symm
      _ =
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
            ‖t‖ *
              (‖(x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹‖ * (1 : ℝ)) := by
        exact congrArg₂ HMul.hMul
          (congrArg (fun r : ℝ =>
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ * r) ha)
          (Eq.trans
            (norm_mul
              ((x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹)
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
            (congrArg
              (fun r : ℝ =>
                ‖(x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹‖ * r)
              hphase))
      _ =
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
            ‖t‖ *
              ‖(x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹‖ := by
        exact congrArg
          (fun r : ℝ =>
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
              ‖t‖ * r)
          (mul_one ‖(x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹‖)
      _ ≤
          (1 : ℝ) * ‖t‖ *
            ((1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ))) := by
        exact mul_le_mul
          (mul_le_mul hB (le_rfl : ‖t‖ ≤ ‖t‖)
            (norm_nonneg t) zero_le_one)
          hrecip
          (norm_nonneg ((x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹))
          (mul_nonneg zero_le_one (norm_nonneg t))
      _ =
          ‖t‖ *
            ((1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ))) := by
        exact congrArg
          (fun r : ℝ =>
            r * ((1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ))))
          (one_mul ‖t‖)
  exact hraw

/-- Lebesgue measure of a natural unit right-endpoint block is one. -/
theorem boundaryGrowth_volume_Ioc_nat_unit_toReal
    (n : ℕ) :
    (volume (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)))).toReal =
      (1 : ℝ) := by
  have hvolume :
      volume (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) =
        ENNReal.ofReal ((((n + 1 : ℕ) : ℝ)) - (((n : ℕ) : ℝ))) :=
    Real.volume_Ioc
  have hlength :
      (((n + 1 : ℕ) : ℝ)) - (((n : ℕ) : ℝ)) = (1 : ℝ) := by
    have hsucc : (((n + 1 : ℕ) : ℝ)) = ((n : ℕ) : ℝ) + (1 : ℝ) :=
      Nat.cast_add_one n
    calc
      (((n + 1 : ℕ) : ℝ)) - (((n : ℕ) : ℝ)) =
          (((n : ℕ) : ℝ) + (1 : ℝ)) - (((n : ℕ) : ℝ)) := by
        exact congrArg (fun r : ℝ => r - (((n : ℕ) : ℝ))) hsucc
      _ = (1 : ℝ) := by
        exact add_sub_cancel_left (((n : ℕ) : ℝ)) 1
  have hofReal :
      ENNReal.ofReal ((((n + 1 : ℕ) : ℝ)) - (((n : ℕ) : ℝ))) =
        ENNReal.ofReal (1 : ℝ) :=
    congrArg ENNReal.ofReal hlength
  have htoReal :
      (ENNReal.ofReal (1 : ℝ)).toReal = (1 : ℝ) :=
    ENNReal.toReal_ofReal zero_le_one
  exact Eq.trans
    (congrArg ENNReal.toReal (Eq.trans hvolume hofReal))
    htoReal

/-- Local reciprocal-drift block estimate in right-endpoint indexing. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDriftBlock_norm_le
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
      ‖t‖ *
        ((1 : ℝ) /
          (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ)))) := by
  let m : ℕ := n - 1
  let s : Set ℝ := Set.Ioc (((m : ℕ) : ℝ)) (((n : ℕ) : ℝ))
  let C : ℝ :=
    ‖t‖ *
      ((1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ)))
  let F : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      ((-(t : ℂ) * Complex.I) *
        (((x : ℂ)⁻¹ -
            (((m : ℕ) : ℝ) : ℂ)⁻¹) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hn_pos : 0 < n :=
    lt_trans hcutoff_pos hcutoff_lt_n
  have hm_succ : m + 1 = n :=
    Nat.sub_add_cancel hn_pos
  have hmeasure :
      (volume s).toReal = (1 : ℝ) := by
    exact Eq.subst
      (motive := fun q : ℕ =>
        (volume (Set.Ioc (((m : ℕ) : ℝ)) (((q : ℕ) : ℝ)))).toReal =
          (1 : ℝ))
      hm_succ
      (boundaryGrowth_volume_Ioc_nat_unit_toReal m)
  have hbound :
      ∀ x ∈ s, ‖F x‖ ≤ C := by
    intro x hx
    exact
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDrift_pointwise_norm_le
        t hn hx
  have hset :
      ‖∫ x in s, F x‖ ≤ C * (volume s).toReal :=
    norm_setIntegral_le_of_norm_le_const'
      measure_Ioc_lt_top
      measurableSet_Ioc
      hbound
  have hcollapse :
      C * (volume s).toReal = C := by
    exact Eq.trans
      (congrArg (fun r : ℝ => C * r) hmeasure)
      (mul_one C)
  exact le_trans hset
    (le_of_eq hcollapse)

/-- Finite reciprocal-drift block sum bound for the selected normalized-kernel
decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDriftBlockSum_norm_le_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
      1 := by
  let R : ℕ → ℂ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          (((x : ℂ)⁻¹ -
              (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
  let S : ℕ → ℝ := fun n =>
    ‖t‖ *
      ((1 : ℝ) /
        (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ))))
  have htriangle :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, R n‖ ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖R n‖ :=
    norm_sum_le (Finset.Ioc ⌊2 + ‖t‖⌋₊ M) R
  have hlocal :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖R n‖) ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, S n :=
    Finset.sum_le_sum
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDriftBlock_norm_le
          t hn)
  have hscalar :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, S n) ≤ 1 :=
    boundaryLineOnePointRealParam_reciprocalVariation_selected_Ioc_sum_le_one
      t ht hM
  exact le_trans htriangle
    (le_trans hlocal hscalar)

/-- Local phase-drift block after pulling out the constant normalized
left-endpoint coefficient.

This is the algebraic owner form needed before applying finite
Dirichlet/Abel cancellation to the remaining Bernoulli-weighted phase
increments. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlock_eq_const_mul_phaseIncrementIntegral
    (t : ℝ)
    {n : ℕ} :
    (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))))) =
      ((-(t : ℂ) * Complex.I) *
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)))))) := by
  let c : ℂ :=
    (-(t : ℂ) * Complex.I) *
      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))
  let s : Set ℝ :=
    Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))
  let F : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I))))
  have hpoint :
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
        (fun x : ℝ => c * F x) := by
    funext x
    let b : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
    let a : ℂ := -(t : ℂ) * Complex.I
    let q : ℂ := (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)
    let d : ℂ :=
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (((((n - 1 : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
    calc
      b * (a * (q * d)) = b * ((a * q) * d) :=
        congrArg (fun z : ℂ => b * z) (mul_assoc a q d).symm
      _ = (b * (a * q)) * d := (mul_assoc b (a * q) d).symm
      _ = ((a * q) * b) * d :=
        congrArg (fun z : ℂ => z * d) (mul_comm b (a * q))
      _ = (a * q) * (b * d) := mul_assoc (a * q) b d
  have hintegral :
      (∫ x in s,
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
        ∫ x in s, c * F x := by
    exact congrArg (fun G : ℝ → ℂ => ∫ x in s, G x) hpoint
  have hconst :
      (∫ x in s, c * F x) = c * ∫ x in s, F x :=
    integral_mul_left c F
  exact Eq.trans hintegral hconst

/-- The constant coefficient in each factored phase-drift block is bounded by
one after the canonical cutoff. -/
theorem boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_norm_le_one
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖((-(t : ℂ) * Complex.I) *
        (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))‖ ≤ (1 : ℝ) := by
  let m : ℕ := n - 1
  let mr : ℝ := ((m : ℕ) : ℝ)
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_le_m : ⌊2 + ‖t‖⌋₊ ≤ m :=
    Nat.le_sub_one_of_lt hcutoff_lt_n
  have hnorm_le_mr :
      ‖t‖ ≤ mr := by
    exact le_trans
      (le_trans
        (le_add_of_nonneg_left (show (0 : ℝ) ≤ 1 from zero_le_one))
        (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t))
      (Nat.cast_le.mpr hcutoff_le_m)
  have hm_pos_nat : 0 < m :=
    lt_of_lt_of_le
      (boundaryLineOnePointRealParam_cutoff_pos t)
      hcutoff_le_m
  have hmr_pos : 0 < mr :=
    Nat.cast_pos.mpr hm_pos_nat
  have hnum :
      ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hinv :
      ‖((mr : ℂ)⁻¹)‖ = mr⁻¹ :=
    boundaryLineOnePointRealParam_complex_inv_ofReal_norm_eq_inv hmr_pos
  have hmul :
      ‖((-(t : ℂ) * Complex.I) * ((mr : ℂ)⁻¹))‖ =
        ‖t‖ * mr⁻¹ := by
    calc
      ‖((-(t : ℂ) * Complex.I) * ((mr : ℂ)⁻¹))‖ =
          ‖(-(t : ℂ) * Complex.I)‖ * ‖((mr : ℂ)⁻¹)‖ := by
        exact norm_mul (-(t : ℂ) * Complex.I) ((mr : ℂ)⁻¹)
      _ = ‖t‖ * ‖((mr : ℂ)⁻¹)‖ := by
        exact congrArg (fun r : ℝ => r * ‖((mr : ℂ)⁻¹)‖) hnum
      _ = ‖t‖ * mr⁻¹ := by
        exact congrArg (fun r : ℝ => ‖t‖ * r) hinv
  have hratio :
      ‖t‖ * mr⁻¹ ≤ (1 : ℝ) := by
    have hdiv : ‖t‖ / mr ≤ (1 : ℝ) :=
      (div_le_one₀ hmr_pos).mpr hnorm_le_mr
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ (1 : ℝ))
      (div_eq_mul_inv ‖t‖ mr)
      hdiv
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ (1 : ℝ))
    hmul.symm
    hratio

/-- Local phase-drift block norm after removing the harmless cutoff-normalized
left-endpoint coefficient. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlock_norm_le_phaseIncrementIntegral_norm
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))))‖ ≤
      ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))‖ := by
  let c : ℂ :=
    (-(t : ℂ) * Complex.I) *
      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))
  let J : ℂ :=
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))))
  have hfactor :
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
        c * J :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlock_eq_const_mul_phaseIncrementIntegral
      t
  have hc : ‖c‖ ≤ (1 : ℝ) :=
    boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_norm_le_one
      t hn
  have hnorm :
      ‖c * J‖ ≤ ‖J‖ := by
    calc
      ‖c * J‖ = ‖c‖ * ‖J‖ := by
        exact norm_mul c J
      _ ≤ (1 : ℝ) * ‖J‖ := by
        exact mul_le_mul hc (le_rfl : ‖J‖ ≤ ‖J‖) (norm_nonneg J) zero_le_one
      _ = ‖J‖ := by
        exact one_mul ‖J‖
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖J‖)
    hfactor.symm
    hnorm

/-- Finite phase-drift block sum after coefficient removal.

This is the summed non-circular reduction of the phase-drift part: the
remaining estimate is exactly the finite Dirichlet/Abel cancellation for the
Bernoulli-weighted phase-increment integrals. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_phaseIncrementIntegralNormSum
    (t : ℝ)
    {M : ℕ} :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))))‖ ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))‖ := by
  let F : ℕ → ℂ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))))
  let G : ℕ → ℂ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))))
  have htriangle :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, F n‖ ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖F n‖ :=
    norm_sum_le (Finset.Ioc ⌊2 + ‖t‖⌋₊ M) F
  have hlocal :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖F n‖) ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖G n‖ :=
    Finset.sum_le_sum
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlock_norm_le_phaseIncrementIntegral_norm
          t hn)
  exact le_trans htriangle hlocal

/-- Local Bernoulli zero-mean cancellation for phase increments.

On each post-cutoff unit block, subtracting the left-endpoint phase does not
change the first-periodic-Bernoulli integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_phaseIntegral
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) =
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  let m : ℕ := n - 1
  let K : ℝ → ℂ := fun x =>
    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hn_pos : 0 < n :=
    lt_trans hcutoff_pos hcutoff_lt_n
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hcutoff_lt_n
  have hm_pos : 0 < m :=
    Nat.sub_pos_of_lt hone_lt_n
  have hsucc : m + 1 = n :=
    Nat.sub_add_cancel hn_pos
  have hle :
      (((m : ℕ) : ℝ)) ≤ (((m + 1 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.le_succ m)
  have hcont_phase :
      ContinuousOn K (Set.Icc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hm_pos) hx.1
    exact
      (Complex.continuousAt_ofReal_cpow_const x (-(t : ℂ) * Complex.I)
        (Or.inr (ne_of_gt hx_pos))).continuousWithinAt
  have hphase_integrable :
      IntegrableOn K
        (Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)))
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (ContinuousOn.intervalIntegrable_of_Icc hle hcont_phase)
  have hBK :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x)
        (volume.restrict
          (Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)))) :=
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      K
      (((m : ℕ) : ℝ))
      (((m + 1 : ℕ) : ℝ))
      hphase_integrable
  let c : ℂ := K (((m : ℕ) : ℝ))
  have hc_integrable :
      IntegrableOn
        (fun constantArgument : ℝ => c)
        (Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)))
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (intervalIntegrable_const
        (μ := volume)
        (a := (((m : ℕ) : ℝ)))
        (b := (((m + 1 : ℕ) : ℝ)))
        (c := c))
  have hBc :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            K (((m : ℕ) : ℝ)))
        (volume.restrict
          (Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)))) :=
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun constantArgument : ℝ => c)
      (((m : ℕ) : ℝ))
      (((m + 1 : ℕ) : ℝ))
      hc_integrable
  have hraw :
      (∫ x in Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (K x - K (((m : ℕ) : ℝ)))) =
        (∫ x in Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x) :=
    (boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtract_leftEndpoint
      m K hBK hBc).symm
  exact
    Eq.subst
      (motive := fun q : ℕ =>
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)))) =
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))
      hsucc
      hraw

/-- Pointwise Taylor-linear decomposition of one logarithmic phase increment.

The first term is the resonance-bearing derivative at the left endpoint; the
second term is the nonlinear local remainder.  This is the source object needed
for the unconditional Dirichlet/Abel block cancellation, before any absolute
movement estimate is taken. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_phaseIncrement_eq_linear_add_remainder
    (t : ℝ)
    (x a : ℝ) :
    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
          (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
          ((x : ℂ) - (a : ℂ)) +
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
            (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
            ((x : ℂ) - (a : ℂ))) := by
  let P : ℂ :=
    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℂ :=
    (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
        (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
        ((x : ℂ) - (a : ℂ))
  calc
    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        P := rfl
    _ = L + (P - L) := by
      have hcancel : L + (P - L) = P :=
        Eq.trans
          (add_sub_assoc L P L).symm
          (add_sub_cancel_left L P)
      exact hcancel.symm
    _ =
      (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
          (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
          ((x : ℂ) - (a : ℂ)) +
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
            (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
            ((x : ℂ) - (a : ℂ))) := rfl

/-- Integral form of the local Taylor-linear phase-block decomposition.

This keeps the first-periodic Bernoulli weight inside the local block while
exposing the derivative-at-left-endpoint main term and the nonlinear remainder.
The later cancellation theorem can now attack the main term by finite
Dirichlet/Abel summation and the remainder by a genuinely smaller local
estimate. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_linear_add_remainder
    (t : ℝ)
    (n : ℕ) :
    (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) =
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((((-(t : ℂ) * Complex.I) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))) *
              ((x : ℂ) -
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))) +
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))) -
              ((((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) *
                ((x : ℂ) -
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)))))))))) := by
  let a : ℝ := ((((n - 1 : ℕ) : ℕ) : ℝ))
  let s : Set ℝ := Set.Ioc a (((n : ℕ) : ℝ))
  let B : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let F : ℝ → ℂ := fun x =>
    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℝ → ℂ := fun x =>
    (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
        (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
        ((x : ℂ) - (a : ℂ))
  have hpoint :
      (fun x : ℝ => B x * F x) =
        (fun x : ℝ => B x * (L x + (F x - L x))) := by
    funext x
    have hphase :
        F x = L x + (F x - L x) :=
      boundaryLineOnePointRealParam_logarithmicPhase_phaseIncrement_eq_linear_add_remainder
        t x a
    exact congrArg (fun z : ℂ => B x * z) hphase
  exact congrArg (fun f : ℝ → ℂ => ∫ x in s, f x) hpoint

/-- Finite post-cutoff sum form of the Taylor-linear phase-block decomposition.

This is the source-level bridge from the current phase-increment block object to
the two pieces used in the eventual resonance-aware estimate: the
left-endpoint derivative main term and the nonlinear Taylor remainder. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_linear_add_remainder
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) =
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) *
                ((x : ℂ) -
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))) +
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) -
                ((((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))) *
                  ((x : ℂ) -
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))))))))) := by
  exact Finset.sum_congr rfl
    (fun n hnMembership =>
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_linear_add_remainder
        t n)

/-- Local integrability of the Bernoulli-weighted logarithmic phase on one
post-cutoff unit block. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_phase_integrable
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    Integrable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hcutoff_lt_n
  have hn_pred_pos : 0 < n - 1 :=
    Nat.sub_pos_of_lt hone_lt_n
  have hle :
      ((((n - 1 : ℕ) : ℕ) : ℝ)) ≤ (((n : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.sub_le n 1)
  have hcont_phase :
      ContinuousOn
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn_pred_pos) hx.1
    exact
      (Complex.continuousAt_ofReal_cpow_const x (-(t : ℂ) * Complex.I)
        (Or.inr (ne_of_gt hx_pos))).continuousWithinAt
  have hphase_integrable :
      IntegrableOn
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (ContinuousOn.intervalIntegrable_of_Icc hle hcont_phase)
  exact
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
      ((((n - 1 : ℕ) : ℕ) : ℝ))
      (((n : ℕ) : ℝ))
      hphase_integrable

/-- Global assembly of the finite Bernoulli-weighted phase-integral blocks.

This is the finite complex object produced after local phase-increment
cancellation; the remaining analytic step is the Dirichlet/Abel bound for this
single post-cutoff oscillatory integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIntegralBlockSum_eq_global
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hcover :
      (⋃ n ∈ Finset.Ioc C M,
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) =
        Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)) :=
    boundaryGrowth_biUnion_Ioc_pred_self_natCast_eq_Ioc C M
  have hsplit :
      (∫ x in ⋃ n ∈ Finset.Ioc C M,
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x) =
        ∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
    boundaryGrowth_integral_finset_biUnion_Ioc_pred_self_natCast
      (Finset.Ioc C M)
      f
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_phase_integrable
          t hn)
  have hdomain :
      (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) =
        ∫ x in ⋃ n ∈ Finset.Ioc C M,
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
    congrArg
      (fun s : Set ℝ => ∫ x in s, f x)
      hcover.symm
  exact
    Eq.symm
      (Eq.trans hdomain hsplit)

/-- Global Bernoulli-weighted phase integral as the finite sum of local
zero-mean phase-increment blocks.

This is the non-absolute cancellation form needed by the Dirichlet/Abel
blocking estimate: each local integral has had its left-endpoint phase removed
using the one-interval Bernoulli zero-mean identity, while the total remains the
single global oscillatory phase integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_globalPhaseIntegral
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) =
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hlocal :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)))) =
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_phaseIntegral
          t hn)
  exact Eq.trans hlocal
    (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIntegralBlockSum_eq_global
      t)

/-- Quantitative transfer from the global Bernoulli-weighted phase integral to
the finite zero-mean phase-increment block sum.

This is the exact non-absolute bridge needed after the global
Dirichlet/Abel/stationary-phase estimate for
`∫ B₁(x) x^{-it}` is proved: no local scalar movement envelope is used. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_of_globalPhaseIntegral
    (t : ℝ)
    {M : ℕ}
    (hphase :
      ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_globalPhaseIntegral
        t).symm
      hphase

/-- Monotonicity of the logarithmic terminal scale on natural endpoints. -/
theorem boundaryLineOnePointRealParam_log_two_add_nat_mono
    {K M : ℕ}
    (hKM : K ≤ M) :
    Real.log (2 + K) ≤ Real.log (2 + M) := by
  have hleft_pos : 0 < (2 : ℝ) + K :=
    lt_of_lt_of_le zero_lt_two
      (le_add_of_nonneg_right (Nat.cast_nonneg K))
  have harg_le : (2 : ℝ) + K ≤ (2 : ℝ) + M :=
    add_le_add_left (Nat.cast_le.mpr hKM) 2
  exact Real.log_le_log hleft_pos harg_le

/-- Local-terminal phase-increment partial-sum bound from the corresponding
global Bernoulli-weighted phase-integral estimates and endpoint monotonicity. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrement_partial_sums_norm_le_of_globalPhaseIntegral_family
    (t : ℝ)
    {M : ℕ}
    (hphase :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) :
    ∀ K : ℕ,
      ⌊2 + ‖t‖⌋₊ ≤ K →
      K ≤ M →
        ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))‖ ≤
          2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  intro K hK hKM
  have hlocal :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + K) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_of_globalPhaseIntegral
      t (hphase K hK hKM)
  have hscale_nonneg :
      0 ≤ 2 * Real.sqrt (1 + ‖t‖) :=
    mul_nonneg (show (0 : ℝ) ≤ 2 from zero_le_two)
      (Real.sqrt_nonneg (1 + ‖t‖))
  have hlog_le :
      Real.log (2 + K) ≤ Real.log (2 + M) :=
    boundaryLineOnePointRealParam_log_two_add_nat_mono hKM
  exact le_trans hlocal
    (mul_le_mul_of_nonneg_left hlog_le hscale_nonneg)

/-- Finite Abel/Dirichlet absorption for the concrete phase-drift block sum.

This is the coefficient-summation step for the actual phase-drift blocks:
`(-it)/(n-1)` is factored into a fixed unit complex direction and the positive
decreasing weight `|t|/(n-1)`, then finite Abel summation is applied to the
unweighted phase-increment block sequence. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_of_phaseIncrement_partial_sums
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    {B : ℝ}
    (hpartial :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
            ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))))‖ ≤ B := by
  let D : ℂ := (-(t : ℂ) * Complex.I) / ((‖t‖ : ℝ) : ℂ)
  let U : ℕ → ℂ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))))
  let W : ℕ → ℂ := fun n =>
    (((‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) : ℝ) : ℂ) * U n)
  have hblock :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))) =
        D * ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n) := by
    have hlocal :
        ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I))))))) =
            D * W n := by
      intro n hn
      have hfactor :
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I))))))) =
            ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) * U n) :=
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlock_eq_const_mul_phaseIncrementIntegral
          t
      have hcoeff :
          ((-(t : ℂ) * Complex.I) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))) =
            D * (((‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) : ℝ) : ℂ)) :=
        boundaryLineOnePointRealParam_phaseDrift_rightEndpointCoefficient_eq_direction_mul_weight
          t ht hn
      calc
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))) =
            ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) * U n) :=
          hfactor
        _ = (D * (((‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) : ℝ) : ℂ)) * U n) := by
          exact congrArg (fun z : ℂ => z * U n) hcoeff
        _ = D * W n := by
          exact mul_assoc D
            (((‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) : ℝ) : ℂ))
            (U n)
    have hsum :
        (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I)))))))) =
          ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, D * W n :=
      Finset.sum_congr rfl hlocal
    exact Eq.trans hsum
      (Finset.mul_sum
        (Finset.Ioc ⌊2 + ‖t‖⌋₊ M)
        W
        D).symm
  have hweighted :
      ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W k‖ ≤ B :=
    boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_finite_sum_norm_le_of_local
      t ht hM U hpartial
  have hD_norm : ‖D‖ = (1 : ℝ) :=
    boundaryLineOnePointRealParam_phaseDrift_coefficientDirection_norm_eq_one
      t ht
  have hmul_bound :
      ‖D * ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖ ≤ B := by
    calc
      ‖D * ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖ =
          ‖D‖ * ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖ := by
        exact norm_mul D (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n)
      _ = (1 : ℝ) * ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖ := by
        exact congrArg
          (fun r : ℝ => r * ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖)
          hD_norm
      _ = ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖ := by
        exact one_mul ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖
      _ ≤ B := hweighted
  exact
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ B)
      hblock.symm
      hmul_bound

/-- Concrete phase-drift block bound from terminal-local global phase-integral
estimates. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_of_globalPhaseIntegral_family
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hphase :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_of_phaseIncrement_partial_sums
      t ht hM
      (B := 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrement_partial_sums_norm_le_of_globalPhaseIntegral_family
        t hphase)

/-- Sharp local-terminal phase-increment partial-sum bound from the
corresponding sharp global Bernoulli-weighted phase-integral estimates.

This is the constant-correct version needed for the selected
normalized-kernel cancellation: the phase-drift side must consume only one
copy of `sqrt (1 + |t|) log (2 + M)`, leaving the other copy to absorb the
reciprocal-drift telescope. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrement_partial_sums_norm_le_of_globalPhaseIntegral_family_sharp
    (t : ℝ)
    {M : ℕ}
    (hphase :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) :
    ∀ K : ℕ,
      ⌊2 + ‖t‖⌋₊ ≤ K →
      K ≤ M →
        ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))‖ ≤
          Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  intro K hK hKM
  have hlocal :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))‖ ≤
        Real.sqrt (1 + ‖t‖) * Real.log (2 + K) :=
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + K))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_globalPhaseIntegral
        t).symm
      (hphase K hK hKM)
  have hscale_nonneg :
      0 ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hlog_le :
      Real.log (2 + K) ≤ Real.log (2 + M) :=
    boundaryLineOnePointRealParam_log_two_add_nat_mono hKM
  exact le_trans hlocal
    (mul_le_mul_of_nonneg_left hlog_le hscale_nonneg)

/-- Sharp finite Abel/Dirichlet phase-drift block bound from sharp
terminal-local global phase-integral estimates. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_of_globalPhaseIntegral_family_sharp
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hphase :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_of_phaseIncrement_partial_sums
      t ht hM
      (B := Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrement_partial_sums_norm_le_of_globalPhaseIntegral_family_sharp
        t hphase)

end
end LFunctions
end Boundary
