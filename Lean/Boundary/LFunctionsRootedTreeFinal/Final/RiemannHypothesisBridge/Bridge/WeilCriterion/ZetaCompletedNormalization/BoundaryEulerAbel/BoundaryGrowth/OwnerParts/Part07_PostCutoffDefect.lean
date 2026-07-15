import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part06_PhaseBlocks

/-!
# Boundary growth owner part 7

This file is a mechanical forward-order split of `BoundaryGrowth.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory
local notation "π" => Real.pi

theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_scalarMovementSum
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                  ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
            ‖t‖ *
              (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_scalarMovementSum_of_integrable
      t
      hM
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_normalizedKernel_integrable
          t hn)
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_leftEndpoint_normalizedKernel_integrable
          t hn)

/-- Finite first-order Euler-Maclaurin identity for the unweighted
logarithmic-phase post-cutoff tail, normalized to the derivative kernel used by
the boundary-line Dirichlet package. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_tail_eulerMaclaurin_normalizedDerivative_ownerGap
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
        (-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hstandard :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          (-(1 / 2 : ℂ) *
            ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-((t : ℂ) * Complex.I) *
                (((x : ℝ) : ℂ) ^
                  (-(((t : ℂ) * Complex.I) + 1))))) := by
    have hphase :
        (-((t : ℂ) * Complex.I)) = (-(t : ℂ) * Complex.I) :=
      (neg_mul (t : ℂ) Complex.I).symm
    have hstandardRaw :=
      eulerMaclaurin_firstOrder_cpow_neg_finite_postCutoffTail_identity_standard
        ((t : ℂ) * Complex.I)
        ⌊2 + ‖t‖⌋₊
        M
        hcutoff_pos
        hM
    exact Eq.subst
      (motive := fun phase : ℂ =>
        (∑ n in Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            (((n : ℕ) : ℝ) : ℂ) ^ phase) =
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              (((x : ℝ) : ℂ) ^ phase)) +
            (-(1 / 2 : ℂ) *
              ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^ phase)) +
            ((1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ phase)) +
            (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (-((t : ℂ) * Complex.I) *
                  (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))))))
      hphase
      hstandardRaw
  have hremainder :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-((t : ℂ) * Complex.I) *
            (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))))) =
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_standard_eq_normalized
      t hM
  exact Eq.trans hstandard
    (congrArg
      (fun R : ℂ =>
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          (-(1 / 2 : ℂ) *
            ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          R)
      hremainder)

/-- Solved-for normalized Bernoulli remainder in the boundary-line finite
Euler-Maclaurin identity.

This is the boundary-growth specialization of the finite Bernoulli
integration-by-parts primitive: the normalized remainder is exactly the
post-cutoff finite sum minus the main integral and the two half-endpoint terms. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_remainderIntegral_eq_tail_sub_integral_sub_endpoints
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
        (-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) -
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) := by
  let S : ℂ :=
    ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)
  let I : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℂ :=
    -(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let U : ℂ :=
    (1 / 2 : ℂ) *
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let R : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hem :
      S = I + L + U + R :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_tail_eulerMaclaurin_normalizedDerivative_ownerGap
      t hM
  have hpeel_I :
      I + L + U + R - I = L + U + R := by
    calc
      I + L + U + R - I =
          (I + (L + U + R)) - I := by
        exact congrArg (fun z : ℂ => z - I)
          (Eq.trans
            (add_assoc (I + L) U R)
            (Eq.trans
              (add_assoc I L (U + R))
              (congrArg (fun z : ℂ => I + z) (add_assoc L U R).symm)))
      _ = L + U + R := by
        exact add_sub_cancel_left I (L + U + R)
  have hpeel_L :
      (L + U + R) - L = U + R := by
    calc
      (L + U + R) - L =
          (L + (U + R)) - L := by
        exact congrArg (fun z : ℂ => z - L)
          (add_assoc L U R)
      _ = U + R := by
        exact add_sub_cancel_left L (U + R)
  have hpeel_U :
      (U + R) - U = R := by
    calc
      (U + R) - U = R + U - U := by
        exact congrArg (fun z : ℂ => z - U) (add_comm U R)
      _ = R := by
        exact add_sub_cancel_right R U
  have hraw :
      (I + L + U + R) - I - L - U = R := by
    calc
      (I + L + U + R) - I - L - U =
          (L + U + R) - L - U := by
        exact congrArg (fun z : ℂ => z - L - U) hpeel_I
      _ = (U + R) - U := by
        exact congrArg (fun z : ℂ => z - U) hpeel_L
      _ = R := hpeel_U
  have hsolved :
      R = S - I - L - U := by
    calc
      R = (I + L + U + R) - I - L - U := hraw.symm
      _ = S - I - L - U := by
        exact congrArg (fun z : ℂ => z - I - L - U) hem.symm
  exact hsolved

/-- Exact post-cutoff Euler-Maclaurin decomposition for the unweighted
logarithmic-phase tail.

The existing post-cutoff Abel theorem controls the weighted tail
`n⁻¹ n^{-it}`.  The public partial-sum bound needs this separate unweighted
identity for `n^{-it}`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_eulerMaclaurin_decomposition_ownerGap
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊ +
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
        (-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hsplit :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊ +
          ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq_prefix_add_Ioc_tail
      t hM
  have htail :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          (-(1 / 2 : ℂ) *
            ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_tail_eulerMaclaurin_normalizedDerivative_ownerGap
      t hM
  let P : ℂ :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊
  let I : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℂ :=
    -(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let U : ℂ :=
    (1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let R : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hprefixTail :
      P + (∑ n in Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        P + (I + L + U + R) :=
    congrArg (fun z : ℂ => P + z) htail
  have hreassociate :
      P + (I + L + U + R) = P + I + L + U + R := by
    calc
      P + (I + L + U + R) = (P + (I + L + U)) + R :=
        (add_assoc P (I + L + U) R).symm
      _ = ((P + (I + L)) + U) + R := by
        exact congrArg (fun z : ℂ => z + R)
          (add_assoc P (I + L) U).symm
      _ = (((P + I) + L) + U) + R := by
        exact congrArg (fun z : ℂ => (z + U) + R)
          (add_assoc P I L).symm
  exact Eq.trans hsplit (Eq.trans hprefixTail hreassociate)

/-- Positive integer endpoint norm for the unweighted antiderivative
`x^(1-it)`. -/
theorem logarithmicPhase_nat_sample_one_minus_it_norm_eq_nat
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖(n : ℂ) ^ (((-(t : ℂ) * Complex.I) + (1 : ℂ)))‖ =
      (n : ℝ) := by
  have hnorm :
      ‖(n : ℂ) ^ (((-(t : ℂ) * Complex.I) + (1 : ℂ)))‖ =
        (n : ℝ) ^
          (((-(t : ℂ) * Complex.I) + (1 : ℂ)).re) :=
    Complex.norm_natCast_cpow_of_pos hn
      (((-(t : ℂ) * Complex.I) + (1 : ℂ)))
  have hre :
      (((-(t : ℂ) * Complex.I) + (1 : ℂ)).re) = (1 : ℝ) := by
    calc
      (((-(t : ℂ) * Complex.I) + (1 : ℂ)).re) =
          (-(t : ℂ) * Complex.I).re + ((1 : ℂ) : ℂ).re := by
        exact Complex.add_re (-(t : ℂ) * Complex.I) (1 : ℂ)
      _ = 0 + ((1 : ℂ) : ℂ).re := by
        have hneg_im : (-(t : ℂ)).im = (0 : ℝ) := by
          exact Eq.trans
            (Complex.neg_im (t : ℂ))
            (Eq.trans
              (congrArg Neg.neg (Complex.ofReal_im t))
              (neg_zero : -(0 : ℝ) = 0))
        have hmul_re : (-(t : ℂ) * Complex.I).re = (0 : ℝ) := by
          exact Eq.trans
            (Complex.mul_I_re (-(t : ℂ)))
            (Eq.trans (congrArg Neg.neg hneg_im) (neg_zero : -(0 : ℝ) = 0))
        exact congrArg (fun r : ℝ => r + ((1 : ℂ) : ℂ).re) hmul_re
      _ = 0 + 1 := by
        exact congrArg (fun r : ℝ => 0 + r) (Complex.ofReal_re 1)
      _ = 1 := by
        exact zero_add 1
  have hpow_one :
      (n : ℝ) ^
          (((-(t : ℂ) * Complex.I) + (1 : ℂ)).re) =
        (n : ℝ) := by
    exact Eq.trans
      (congrArg (fun r : ℝ => (n : ℝ) ^ r) hre)
      (Real.rpow_one (n : ℝ))
  exact Eq.trans hnorm hpow_one

/-- The denominator `1 - it` dominates the vertical frequency. -/
theorem logarithmicPhase_norm_le_one_minus_it_norm
    (t : ℝ) :
    ‖t‖ ≤ ‖((-(t : ℂ) * Complex.I) + (1 : ℂ))‖ := by
  let D : ℂ := (-(t : ℂ) * Complex.I) + (1 : ℂ)
  have hD_im : D.im = -t := by
    calc
      D.im = (-(t : ℂ) * Complex.I).im + ((1 : ℂ) : ℂ).im := by
        exact Complex.add_im (-(t : ℂ) * Complex.I) (1 : ℂ)
      _ = (-(t : ℂ)).re + ((1 : ℂ) : ℂ).im := by
        exact congrArg (fun r : ℝ => r + ((1 : ℂ) : ℂ).im)
          (Complex.mul_I_im (-(t : ℂ)))
      _ = -((t : ℂ).re) + ((1 : ℂ) : ℂ).im := by
        exact congrArg (fun r : ℝ => r + ((1 : ℂ) : ℂ).im)
          (Complex.neg_re (t : ℂ))
      _ = -t + ((1 : ℂ) : ℂ).im := by
        exact congrArg (fun r : ℝ => -r + ((1 : ℂ) : ℂ).im)
          (Complex.ofReal_re t)
      _ = -t + 0 := by
        exact congrArg (fun r : ℝ => -t + r) (Complex.ofReal_im 1)
      _ = -t := by
        exact add_zero (-t)
  have habs_im_le_abs : |D.im| ≤ Complex.abs D :=
    Complex.abs_im_le_abs D
  have hnorm_eq_abs : ‖D‖ = Complex.abs D :=
    Complex.norm_eq_abs D
  have hfreq :
      ‖t‖ = |D.im| := by
    have hnorm_real : ‖t‖ = |t| :=
      Real.norm_eq_abs t
    have habs_neg : |-t| = |t| :=
      abs_neg t
    exact Eq.trans hnorm_real
      (Eq.trans habs_neg.symm (congrArg abs hD_im.symm))
  calc
    ‖t‖ = |D.im| := hfreq
    _ ≤ Complex.abs D := habs_im_le_abs
    _ = ‖D‖ := hnorm_eq_abs.symm

/-- Main-integral estimate in the unweighted post-cutoff Dirichlet package.

The `M / |t|` term is the unavoidable primitive size of `x^{-it}`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_mainIntegral_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
        Real.log (2 + M) := by
  have hraw :
      (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ((((((M : ℕ) : ℝ) : ℂ) ^ ((-(t : ℂ) * Complex.I) + (1 : ℂ))) -
            (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              ((-(t : ℂ) * Complex.I) + (1 : ℂ))))) /
          ((-(t : ℂ) * Complex.I) + (1 : ℂ))) := by
    exact
      integral_cpow
        (a := (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)))
        (b := (((M : ℕ) : ℝ)))
        (r := (-(t : ℂ) * Complex.I))
        (Or.inr
          ⟨by
            intro hsing
            have hsing_add :
                (-(t : ℂ) * Complex.I) + (1 : ℂ) =
                  (-1 : ℂ) + (1 : ℂ) :=
              congrArg (fun z : ℂ => z + (1 : ℂ)) hsing
            have hleft :
                (-(t : ℂ) * Complex.I) + (1 : ℂ) =
                  (1 : ℂ) + (-(t : ℂ) * Complex.I) :=
              add_comm (-(t : ℂ) * Complex.I) (1 : ℂ)
            have hright :
                (-1 : ℂ) + (1 : ℂ) = (0 : ℂ) :=
              neg_add_cancel (1 : ℂ)
            have hone_minus_it_zero :
                (1 : ℂ) + (-(t : ℂ) * Complex.I) = (0 : ℂ) :=
              Eq.trans hleft.symm (Eq.trans hsing_add hright)
            have hre :
                ((1 : ℂ) + (-(t : ℂ) * Complex.I)).re =
                  ((0 : ℂ) : ℂ).re :=
              congrArg Complex.re hone_minus_it_zero
            have hleft_re :
                ((1 : ℂ) + (-(t : ℂ) * Complex.I)).re = (1 : ℝ) := by
              calc
                ((1 : ℂ) + (-(t : ℂ) * Complex.I)).re =
                    ((1 : ℂ) : ℂ).re + (-(t : ℂ) * Complex.I).re := by
                  exact Complex.add_re (1 : ℂ) (-(t : ℂ) * Complex.I)
                _ = 1 + (-(t : ℂ) * Complex.I).re := by
                  exact congrArg (fun r : ℝ => r + (-(t : ℂ) * Complex.I).re)
                    (Complex.ofReal_re 1)
                _ = 1 + 0 := by
                  have hneg_im : (-(t : ℂ)).im = (0 : ℝ) := by
                    exact Eq.trans
                      (Complex.neg_im (t : ℂ))
                      (Eq.trans
                        (congrArg Neg.neg (Complex.ofReal_im t))
                        (neg_zero : -(0 : ℝ) = 0))
                  have hmul_re :
                      (-(t : ℂ) * Complex.I).re = (0 : ℝ) := by
                    exact Eq.trans
                      (Complex.mul_I_re (-(t : ℂ)))
                      (Eq.trans
                        (congrArg Neg.neg hneg_im)
                        (neg_zero : -(0 : ℝ) = 0))
                  exact congrArg (fun r : ℝ => 1 + r) hmul_re
                _ = 1 := by
                  exact add_zero 1
            have hright_re :
                ((0 : ℂ) : ℂ).re = (0 : ℝ) :=
              Complex.zero_re
            have hone_eq_zero : (1 : ℝ) = 0 :=
              Eq.trans hleft_re.symm (Eq.trans hre hright_re)
            exact one_ne_zero hone_eq_zero,
            boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_zero_not_mem_uIcc
              t hM⟩)
  have htransport :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    (intervalIntegral.integral_of_le
      (f := fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
      (Nat.cast_le.mpr hM)).symm
  let U : ℂ :=
    ((((M : ℕ) : ℝ) : ℂ) ^ ((-(t : ℂ) * Complex.I) + (1 : ℂ)))
  let L : ℂ :=
    (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
      ((-(t : ℂ) * Complex.I) + (1 : ℂ))))
  let D : ℂ := (-(t : ℂ) * Complex.I) + (1 : ℂ)
  have hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        (U - L) / D :=
    Eq.trans htransport hraw
  have hU_norm : ‖U‖ ≤ (M : ℝ) := by
    have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
      boundaryLineOnePointRealParam_cutoff_pos t
    have hM_pos : 0 < M :=
      lt_of_lt_of_le hcutoff_pos hM
    exact le_of_eq
      (logarithmicPhase_nat_sample_one_minus_it_norm_eq_nat t hM_pos)
  have hL_norm : ‖L‖ ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) := by
    exact le_of_eq
      (logarithmicPhase_nat_sample_one_minus_it_norm_eq_nat t
        (boundaryLineOnePointRealParam_cutoff_pos t))
  have hcutoff_le_M :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (M : ℝ) :=
    Nat.cast_le.mpr hM
  have hnum_le :
      ‖U - L‖ ≤ (2 : ℝ) * (M : ℝ) := by
    have htriangle : ‖U - L‖ ≤ ‖U‖ + ‖L‖ :=
      norm_sub_le U L
    have hendpoints : ‖U‖ + ‖L‖ ≤ (M : ℝ) + (M : ℝ) :=
      add_le_add hU_norm (le_trans hL_norm hcutoff_le_M)
    have htwice : (M : ℝ) + (M : ℝ) = (2 : ℝ) * (M : ℝ) := by
      exact (two_mul (M : ℝ)).symm
    exact le_trans htriangle
      (Eq.subst
        (motive := fun r : ℝ => ‖U‖ + ‖L‖ ≤ r)
        htwice
        hendpoints)
  have hD_norm_ge_t : ‖t‖ ≤ ‖D‖ := by
    exact logarithmicPhase_norm_le_one_minus_it_norm t
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one ht) hD_norm_ge_t
  have hquot_le :
      ‖(U - L) / D‖ ≤ ((2 : ℝ) * (M : ℝ)) / ‖D‖ := by
    have hquot_norm : ‖(U - L) / D‖ = ‖U - L‖ / ‖D‖ :=
      norm_div (U - L) D
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ ((2 : ℝ) * (M : ℝ)) / ‖D‖)
      hquot_norm.symm
      (div_le_div_of_nonneg_right hnum_le (le_of_lt hD_pos))
  have hquot_le_t :
      ((2 : ℝ) * (M : ℝ)) / ‖D‖ ≤ ((2 : ℝ) * (M : ℝ)) / ‖t‖ := by
    have hnum_nonneg : 0 ≤ (2 : ℝ) * (M : ℝ) :=
      mul_nonneg zero_le_two (Nat.cast_nonneg M)
    have ht_pos : 0 < ‖t‖ :=
      lt_of_lt_of_le zero_lt_one ht
    exact div_le_div_of_nonneg_left hnum_nonneg ht_pos hD_norm_ge_t
  have hmain_le :
      ‖(U - L) / D‖ ≤ (2 : ℝ) * ((M : ℝ) / ‖t‖) :=
    have hmul_div :
        ((2 : ℝ) * (M : ℝ)) / ‖t‖ =
          (2 : ℝ) * ((M : ℝ) / ‖t‖) :=
      mul_div_assoc (2 : ℝ) (M : ℝ) ‖t‖
    le_trans hquot_le
      (Eq.subst
        (motive := fun r : ℝ => ((2 : ℝ) * (M : ℝ)) / ‖D‖ ≤ r)
        hmul_div
        hquot_le_t)
  have hlog_lower : (1 : ℝ) ≤ Real.log (2 + M) := by
    have hM_ge_one_add_norm :
        (1 : ℝ) + ‖t‖ ≤ (M : ℝ) :=
      le_trans
        (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t)
        (Nat.cast_le.mpr hM)
    have harg_le :
        2 + ‖t‖ ≤ (2 : ℝ) + M := by
      have hone_add_one :
          (1 : ℝ) + 1 = 2 :=
        one_add_one_eq_two
      have htwo_add_norm :
          2 + ‖t‖ = 1 + (1 + ‖t‖) := by
        calc
          2 + ‖t‖ = ((1 : ℝ) + 1) + ‖t‖ := by
            exact congrArg (fun x : ℝ => x + ‖t‖) hone_add_one.symm
          _ = 1 + (1 + ‖t‖) := by
            exact add_assoc (1 : ℝ) 1 ‖t‖
      calc
        2 + ‖t‖ = 1 + (1 + ‖t‖) :=
          htwo_add_norm
        _ ≤ 1 + (M : ℝ) :=
          add_le_add_left hM_ge_one_add_norm 1
        _ ≤ 2 + (M : ℝ) :=
          add_le_add_right (show (1 : ℝ) ≤ 2 from one_le_two) (M : ℝ)
    have harg_pos : 0 < 2 + ‖t‖ :=
      lt_of_lt_of_le zero_lt_two
        (le_add_of_nonneg_right (norm_nonneg t))
    exact le_trans
      (one_le_log_two_add_norm_of_one_le_norm ht)
      (Real.log_le_log harg_pos harg_le)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hbase_le :
      (2 : ℝ) * ((M : ℝ) / ‖t‖) ≤
        2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) := by
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right hsqrt_nonneg)
      zero_le_two
  have htarget_ge_base :
      (2 : ℝ) * ((M : ℝ) / ‖t‖) ≤
        2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + M) := by
    have hleft_nonneg :
        0 ≤ 2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) :=
      mul_nonneg zero_le_two
        (add_nonneg
          (div_nonneg (Nat.cast_nonneg M) (norm_nonneg t))
          hsqrt_nonneg)
    calc
      (2 : ℝ) * ((M : ℝ) / ‖t‖) ≤
          2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) :=
        hbase_le
      _ = 2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) * 1 := by
        exact (mul_one
          (2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))).symm
      _ ≤ 2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + M) :=
        mul_le_mul_of_nonneg_left hlog_lower hleft_nonneg
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤
        2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + M))
    hidentity.symm
    (le_trans hmain_le htarget_ge_base)

/-- Endpoint estimate for the two half-boundary terms in the unweighted
post-cutoff Euler-Maclaurin decomposition. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_endpoints_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(-(1 / 2 : ℂ) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I))) +
      ((1 / 2 : ℂ) *
        ((((M : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I)))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let L : ℂ :=
    -(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let U : ℂ :=
    (1 / 2 : ℂ) *
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  have hL : ‖L‖ ≤ (1 : ℝ) :=
    let ε : ℂ := -(1 / 2 : ℂ)
    let P : ℂ :=
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
    have hmul : ‖ε * P‖ = ‖ε‖ * ‖P‖ :=
      norm_mul ε P
    have hε : ‖ε‖ ≤ (1 : ℝ) :=
      boundaryGrowth_complex_neg_one_div_two_norm_le_one
    have hP : ‖P‖ ≤ (1 : ℝ) :=
      logarithmicPhase_nat_sample_norm_le_one t ⌊2 + ‖t‖⌋₊
    have hprod : ‖ε‖ * ‖P‖ ≤ (1 : ℝ) * (1 : ℝ) :=
      mul_le_mul hε hP (norm_nonneg P) zero_le_one
    have hone_mul : (1 : ℝ) * (1 : ℝ) = (1 : ℝ) :=
      one_mul (1 : ℝ)
    Eq.subst
      (motive := fun r : ℝ => r ≤ (1 : ℝ))
      hmul.symm
      (Eq.subst
        (motive := fun r : ℝ => ‖ε‖ * ‖P‖ ≤ r)
        hone_mul
        hprod)
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hM_pos : 0 < M :=
    lt_of_lt_of_le hcutoff_pos hM
  have hU : ‖U‖ ≤ (1 : ℝ) :=
    let ε : ℂ := (1 / 2 : ℂ)
    let P : ℂ :=
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
    have hmul : ‖ε * P‖ = ‖ε‖ * ‖P‖ :=
      norm_mul ε P
    have hε : ‖ε‖ ≤ (1 : ℝ) :=
      boundaryGrowth_complex_one_div_two_norm_le_one
    have hP : ‖P‖ ≤ (1 : ℝ) :=
      logarithmicPhase_nat_sample_norm_le_one t M
    have hprod : ‖ε‖ * ‖P‖ ≤ (1 : ℝ) * (1 : ℝ) :=
      mul_le_mul hε hP (norm_nonneg P) zero_le_one
    have hone_mul : (1 : ℝ) * (1 : ℝ) = (1 : ℝ) :=
      one_mul (1 : ℝ)
    Eq.subst
      (motive := fun r : ℝ => r ≤ (1 : ℝ))
      hmul.symm
      (Eq.subst
        (motive := fun r : ℝ => ‖ε‖ * ‖P‖ ≤ r)
        hone_mul
        hprod)
  have hsum : ‖L + U‖ ≤ (2 : ℝ) := by
    have htriangle : ‖L + U‖ ≤ ‖L‖ + ‖U‖ :=
      norm_add_le L U
    have hadd : ‖L‖ + ‖U‖ ≤ (2 : ℝ) := by
      calc
        ‖L‖ + ‖U‖ ≤ (1 : ℝ) + 1 :=
          add_le_add hL hU
        _ = (2 : ℝ) :=
          one_add_one_eq_two
    exact le_trans htriangle hadd
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_le_one_add_norm : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact Real.one_le_sqrt.mpr hone_le_one_add_norm
  have hM_ge_one_add_norm :
      (1 : ℝ) + ‖t‖ ≤ (M : ℝ) :=
    le_trans
      (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t)
      (Nat.cast_le.mpr hM)
  have harg_le :
      2 + ‖t‖ ≤ (2 : ℝ) + M := by
    have hone_add_one :
        (1 : ℝ) + 1 = 2 :=
      one_add_one_eq_two
    have htwo_add_norm :
        2 + ‖t‖ = 1 + (1 + ‖t‖) := by
      calc
        2 + ‖t‖ = ((1 : ℝ) + 1) + ‖t‖ := by
          exact congrArg (fun x : ℝ => x + ‖t‖) hone_add_one.symm
        _ = 1 + (1 + ‖t‖) := by
          exact add_assoc (1 : ℝ) 1 ‖t‖
    calc
      2 + ‖t‖ = 1 + (1 + ‖t‖) :=
        htwo_add_norm
      _ ≤ 1 + (M : ℝ) :=
        add_le_add_left hM_ge_one_add_norm 1
      _ ≤ 2 + (M : ℝ) :=
        add_le_add_right (show (1 : ℝ) ≤ 2 from one_le_two) (M : ℝ)
  have hlog_lower_norm : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hlog_lower_M : (1 : ℝ) ≤ Real.log (2 + M) := by
    have harg_pos : 0 < 2 + ‖t‖ := by
      exact lt_of_lt_of_le zero_lt_two
        (le_add_of_nonneg_right (norm_nonneg t))
    have hlog_le :
        Real.log (2 + ‖t‖) ≤ Real.log (2 + M) :=
      Real.log_le_log harg_pos harg_le
    exact le_trans hlog_lower_norm hlog_le
  have hfactor_ge_one :
      (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
    have hproduct :
        (1 : ℝ) * 1 ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
      mul_le_mul hsqrt_ge_one hlog_lower_M zero_le_one
        (le_trans zero_le_one hsqrt_ge_one)
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      (one_mul (1 : ℝ))
      hproduct
  have hrhs_ge_two :
      (2 : ℝ) ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
    calc
      (2 : ℝ) = 2 * 1 := by
        exact (mul_one 2).symm
      _ ≤ 2 * (Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :=
        mul_le_mul_of_nonneg_left hfactor_ge_one zero_le_two
      _ = 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
        (mul_assoc 2 (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm
  exact le_trans hsum hrhs_ge_two

/-- Exact selected endpoint/variation split from the solved-form finite
Bernoulli integration-by-parts identity.

The endpoint term is the negative of the two half-endpoint corrections, and
the variation term is the finite oscillatory defect `tail sum - main integral`.
This is the canonical split needed by the quantitative owner theorem below. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_exactSplit_endpointBound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      C =
        -((-(1 / 2 : ℂ) *
            ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) ∧
      V =
        (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let S : ℂ :=
    ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)
  let I : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℂ :=
    -(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let U : ℂ :=
    (1 / 2 : ℂ) *
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let C : ℂ := -(L + U)
  let V : ℂ := S - I
  have hsolved :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        S - I - L - U :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_remainderIntegral_eq_tail_sub_integral_sub_endpoints
      t hM
  have hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V := by
    have halg :
        S - I - L - U = C + V := by
      calc
        S - I - L - U =
            (S - I) - (L + U) := by
          exact sub_sub (S - I) L U
        _ = (S - I) + -(L + U) := by
          exact sub_eq_add_neg (S - I) (L + U)
        _ = -(L + U) + (S - I) := by
          exact add_comm (S - I) (-(L + U))
        _ = C + V := rfl
    exact Eq.trans hsolved halg
  have hendpoint_raw :
      ‖L + U‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_endpoints_norm_le_ownerGap
      t ht hM
  have hendpoint :
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
    have hnorm : ‖C‖ = ‖L + U‖ :=
      norm_neg (L + U)
    exact Eq.subst
      (motive := fun r : ℝ =>
        r ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      hnorm.symm
      hendpoint_raw
  exact
    Exists.intro C
      (Exists.intro V
        ⟨hidentity, rfl, rfl, hendpoint⟩)

/-- Exact reconstruction of the finite oscillatory defect from the two
Euler-Maclaurin half-endpoints and the normalized Bernoulli remainder.

This is the first non-circular source step toward the post-cutoff defect
estimate: the remaining analytic work is to bound the normalized Bernoulli
remainder itself. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_defect_eq_endpoints_add_normalizedRemainder
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      ((-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) +
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  let S : ℂ :=
    ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)
  let I : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℂ :=
    -(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let U : ℂ :=
    (1 / 2 : ℂ) *
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let R : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hR :
      R = S - I - L - U :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_remainderIntegral_eq_tail_sub_integral_sub_endpoints
      t hM
  have halg :
      S - I = (L + U) + R := by
    have hsub_pair :
        S - I - L - U = (S - I) - (L + U) :=
      sub_sub (S - I) L U
    have hR_pair :
        R = (S - I) - (L + U) :=
      Eq.trans hR hsub_pair
    calc
      S - I =
          ((S - I) - (L + U)) + (L + U) := by
        exact (sub_add_cancel (S - I) (L + U)).symm
      _ = (L + U) + ((S - I) - (L + U)) := by
        exact add_comm ((S - I) - (L + U)) (L + U)
      _ = (L + U) + R := by
        exact congrArg (fun z : ℂ => (L + U) + z) hR_pair.symm
  exact halg

/-- Triangle inequality form of the exact post-cutoff defect reconstruction.

This reduces the finite oscillatory defect estimate to two genuine pieces:
the already proved endpoint estimate and the remaining normalized Bernoulli
remainder estimate. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_defect_norm_le_endpoints_add_normalizedRemainder
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ‖((-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))))‖ +
        ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ := by
  let E : ℂ :=
    (-(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))) +
      ((1 / 2 : ℂ) *
        ((((M : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I)))
  let R : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hdefect :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        E + R :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_defect_eq_endpoints_add_normalizedRemainder
      t hM
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖E‖ + ‖R‖)
    hdefect.symm
    (norm_add_le E R)

/-- Absorption of the normalized Bernoulli remainder cancellation estimate into
the finite post-cutoff oscillatory defect bound.

This is the exact owner-level bridge needed by the selected endpoint/variation
theorem: after the Euler-Maclaurin endpoint terms are bounded by
`2 * sqrt(1 + |t|) * log(2 + M)`, it remains only to prove the genuine
oscillatory blocking estimate for the normalized Bernoulli remainder with the
same `2 * sqrt(1 + |t|) * log(2 + M)` scale. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_finiteDefect_norm_le_of_normalizedRemainder_blockCancellation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hblock :
      ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖(∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let A : ℝ := Real.sqrt (1 + ‖t‖) * Real.log (2 + M)
  let E : ℂ :=
    (-(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))) +
      ((1 / 2 : ℂ) *
        ((((M : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I)))
  let R : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hdefect :
      ‖(∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        ‖E‖ + ‖R‖ :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_defect_norm_le_endpoints_add_normalizedRemainder
      t hM
  have hendpoint :
      ‖E‖ ≤ 2 * A := by
    have hrawEndpoint :
        ‖E‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_endpoints_norm_le_ownerGap
        t ht hM
    have hscale :
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) = 2 * A :=
      mul_assoc (2 : ℝ) (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))
    exact Eq.subst
      (motive := fun r : ℝ => ‖E‖ ≤ r)
      hscale
      hrawEndpoint
  have hremainder :
      ‖R‖ ≤ 2 * A := by
    have hscale :
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) = 2 * A :=
      mul_assoc (2 : ℝ) (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))
    exact Eq.subst
      (motive := fun r : ℝ => ‖R‖ ≤ r)
      hscale
      hblock
  have hsum :
      ‖E‖ + ‖R‖ ≤ 2 * A + 2 * A :=
    add_le_add hendpoint hremainder
  have htwo_two :
      2 * A + 2 * A = 4 * A := by
    calc
      2 * A + 2 * A = ((2 : ℝ) + 2) * A := by
        exact (add_mul (2 : ℝ) 2 A).symm
      _ = 4 * A := by
        exact congrArg (fun c : ℝ => c * A)
          (two_add_two_eq_four : (2 : ℝ) + 2 = 4)
  have hcombined :
      ‖E‖ + ‖R‖ ≤ 4 * A := by
    calc
      ‖E‖ + ‖R‖ ≤ 2 * A + 2 * A := hsum
      _ = 4 * A := htwo_two
  have htarget :
      4 * A = 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    (mul_assoc (4 : ℝ) (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm
  calc
    ‖(∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        ‖E‖ + ‖R‖ := hdefect
    _ ≤ 4 * A := hcombined
    _ = 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := htarget

/-- Quantitative selected endpoint/variation package reduced to the true
finite oscillatory defect estimate.

The exact split theorem above identifies the variation term as
`tail sum - main integral`.  Thus the only remaining analytic input is the
displayed defect bound; no scalar Bernoulli majorant is used here. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_of_finiteDefect
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hdefect :
      ‖(∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  match
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_exactSplit_endpointBound
      t ht hM with
  | ⟨C, V, hidentity, hCEq, hV_eq, hC_bound⟩ =>
      have hV_bound :
          ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
        exact Eq.subst
          (motive := fun z : ℂ =>
            ‖z‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
          hV_eq.symm
          hdefect
      exact Exists.intro C
        (Exists.intro V
          ⟨hidentity, hC_bound, hV_bound⟩)

/-- Canonical fixed-interval endpoint/variation package reduced to the
normalized Bernoulli block-cancellation estimate.

This is the exact bridge from the true oscillatory cancellation theorem to the
selected endpoint/variation surface. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_of_blockCancellation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hblock :
      ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hdefect :
      ‖(∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_finiteDefect_norm_le_of_normalizedRemainder_blockCancellation
      t ht hM hblock
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_of_finiteDefect
      t ht hM hdefect


end
end LFunctions
end Boundary
