import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.BernoulliCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.HalfPlaneTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.OneIntervalBernoulli
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FiniteIntervalAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffHolomorphic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.LocalMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.ParameterDerivativeMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffBernoulliHolomorphic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PuncturedStripTopology

/-!
# Euler-Maclaurin post-cutoff tail layer

This file owns the finite-to-infinite post-cutoff Euler-Maclaurin tail
construction.  It is split out of `EulerMaclaurinFormula.Owner` so the generic
tail theorem can elaborate before the downstream zeta specialization layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Filter MeasureTheory Set
local notation "π" => Real.pi

/-- Summing the one-interval first-periodic-Bernoulli identities over
`n = N, ..., M - 1` gives the finite natural-interval `Ioc` identity.  This
lemma owns the finite interval partition, additivity of adjacent `Ioc`
integrals, and endpoint telescoping. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_sum_oneInterval_Ioc_from_local
    (f f' : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hf_cont : ContinuousOn f
      (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))))
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x)
    (hf'_int : IntegrableOn f'
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)))) :
    (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) =
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) +
        (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
        ((1 / 2 : ℂ) * f (((M : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
  let P : ℕ → Prop := fun K : ℕ =>
    N ≤ K →
      ContinuousOn f (Set.Icc (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ))) →
      (∀ x : ℝ,
        x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ)) →
          HasDerivAt f (f' x) x) →
      IntegrableOn f' (Set.Ioc (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ))) →
      (∑ n in Finset.Ioc N K, f ((n : ℕ) : ℝ)) =
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ)), f x) +
          (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
          ((1 / 2 : ℂ) * f (((K : ℕ) : ℝ))) +
          (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x)
  have hbase : P N := by
    intro hNN hf_cont_N hf_deriv_N hf'_int_N
    exact eulerMaclaurin_firstPeriodicBernoulli_sum_oneInterval_Ioc_base
      f f' N
  have hstep : ∀ K : ℕ, N ≤ K → P K → P (K + 1) := by
    intro K hNK hIH
    intro hNsucc hf_cont_succ hf_deriv_succ hf'_int_succ
    have hf_cont_left :
        ContinuousOn f
          (Set.Icc (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ))) :=
      eulerMaclaurin_continuousOn_Icc_left_of_succ
        f N K hNK hf_cont_succ
    have hf_cont_right :
        ContinuousOn f
          (Set.Icc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ)))) :=
      eulerMaclaurin_continuousOn_Icc_right_of_succ
        f N K hNK hf_cont_succ
    have hf_deriv_left :
        ∀ x : ℝ,
          x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ)) →
            HasDerivAt f (f' x) x :=
      eulerMaclaurin_deriv_Ioo_left_of_succ
        f f' N K hf_deriv_succ
    have hf_deriv_right :
        ∀ x : ℝ,
          x ∈ Set.Ioo (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))) →
            HasDerivAt f (f' x) x :=
      eulerMaclaurin_deriv_Ioo_right_of_succ
        f f' N K hNK hf_deriv_succ
    have hf'_int_left :
        IntegrableOn f'
          (Set.Ioc (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ))) :=
      eulerMaclaurin_integrableOn_Ioc_left_of_succ
        f' N K hNK hf'_int_succ
    have hf'_int_right :
        IntegrableOn f'
          (Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ)))) :=
      eulerMaclaurin_integrableOn_Ioc_right_of_succ
        f' N K hNK hf'_int_succ
    have hleft :
        (∑ n in Finset.Ioc N K, f ((n : ℕ) : ℝ)) =
          (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ)), f x) +
            (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
            ((1 / 2 : ℂ) * f (((K : ℕ) : ℝ))) +
            (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) :=
      hIH hNK hf_cont_left hf_deriv_left hf'_int_left
    have hright_raw :
        f ((((K + 1 : ℕ) : ℝ))) =
          (∫ x in Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))), f x) +
            (-(1 / 2 : ℂ) * f (((K : ℕ) : ℝ))) +
            (1 / 2 : ℂ) * f ((((K + 1 : ℕ) : ℝ))) +
            ∫ x in Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x :=
      eulerMaclaurin_firstPeriodicBernoulli_oneInterval_integrationByParts
        f f' K hf_cont_right hf_deriv_right hf'_int_right
    have hright :
        f ((((K + 1 : ℕ) : ℝ))) =
          (∫ x in Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))), f x) +
            (-(1 / 2 : ℂ) * f (((K : ℕ) : ℝ))) +
            ((1 / 2 : ℂ) * f ((((K + 1 : ℕ) : ℝ))) +
            ∫ x in Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
      calc
        f ((((K + 1 : ℕ) : ℝ))) =
            (∫ x in Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))), f x) +
              (-(1 / 2 : ℂ) * f (((K : ℕ) : ℝ))) +
              (1 / 2 : ℂ) * f ((((K + 1 : ℕ) : ℝ))) +
              ∫ x in Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x :=
          hright_raw
        _ =
            (∫ x in Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))), f x) +
              (-(1 / 2 : ℂ) * f (((K : ℕ) : ℝ))) +
              ((1 / 2 : ℂ) * f ((((K + 1 : ℕ) : ℝ))) +
              ∫ x in Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
          exact add_assoc
            ((∫ x in Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))), f x) +
              (-(1 / 2 : ℂ) * f (((K : ℕ) : ℝ))))
            ((1 / 2 : ℂ) * f ((((K + 1 : ℕ) : ℝ))))
            (∫ x in Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x)
    have hf_left_int : IntegrableOn f
        (Set.Ioc (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ))) := by
      exact
        (ContinuousOn.integrableOn_Icc hf_cont_left).mono_set
          Ioc_subset_Icc_self
    have hf_right_int : IntegrableOn f
        (Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ)))) := by
      exact
        (ContinuousOn.integrableOn_Icc hf_cont_right).mono_set
          Ioc_subset_Icc_self
    have hrem_left_int : IntegrableOn
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x)
        (Set.Ioc (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ))) :=
      eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
        f' (((N : ℕ) : ℝ)) (((K : ℕ) : ℝ)) hf'_int_left
    have hrem_right_int : IntegrableOn
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x)
        (Set.Ioc (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ)))) :=
      eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
        f' (((K : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))) hf'_int_right
    calc
      (∑ n in Finset.Ioc N (K + 1), f ((n : ℕ) : ℝ)) =
          (∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))), f x) +
            (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
            ((1 / 2 : ℂ) * f ((((K + 1 : ℕ) : ℝ))) +
            ∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) :=
        eulerMaclaurin_firstPeriodicBernoulli_sum_oneInterval_Ioc_succ
          f f' N K hNK hleft hright
          hf_left_int hf_right_int hrem_left_int hrem_right_int
      _ =
          (∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))), f x) +
            (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
            (1 / 2 : ℂ) * f ((((K + 1 : ℕ) : ℝ))) +
            ∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x := by
        exact
          (add_assoc
            ((∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))), f x) +
              (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))))
            ((1 / 2 : ℂ) * f ((((K + 1 : ℕ) : ℝ))))
            (∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((((K + 1 : ℕ) : ℝ))),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x)).symm
  exact Nat.le_induction hbase hstep M hNM hNM hf_cont hf_deriv hf'_int

/-- Finite summation of the one-interval first-periodic-Bernoulli
integration-by-parts identities over a natural `Ioc` interval.

Summing the local formula over `n = N, ..., M - 1` telescopes the half-endpoint
terms to `- f(N)/2 + f(M)/2`, matching the strict post-cutoff convention
`N < n ≤ M`. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_sum_oneInterval_Ioc
    (f f' : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hf_cont : ContinuousOn f
      (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))))
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x)
    (hf'_int : IntegrableOn f'
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)))) :
    (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) =
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) +
        (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
        ((1 / 2 : ℂ) * f (((M : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
  exact
    eulerMaclaurin_firstPeriodicBernoulli_sum_oneInterval_Ioc_from_local
      f f' N M hNM hf_cont hf_deriv hf'_int

/-- First-periodic-Bernoulli integration-by-parts form of the finite
first-order Euler-Maclaurin formula on a natural `Ioc` interval.

This is the genuine finite calculus theorem behind the owner formula: on each
unit interval the derivative of `x - n - 1/2` is `1`, and summing the resulting
integration-by-parts identities gives the `Ioc` endpoint signs. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_integrationByParts_Ioc
    (f f' : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hf_cont : ContinuousOn f
      (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))))
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x)
    (hf'_int : IntegrableOn f'
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)))) :
    (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) =
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) +
        (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
        ((1 / 2 : ℂ) * f (((M : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
  exact
    eulerMaclaurin_firstPeriodicBernoulli_sum_oneInterval_Ioc
      f f' N M hNM hf_cont hf_deriv hf'_int

/-- Generic finite first-order Euler-Maclaurin identity on a natural `Ioc`
interval, with the first periodic Bernoulli remainder.

This is the exact finite calculus theorem needed by the zeta specialization:
the function is continuous on the compact interval, has the stated derivative
on the open interval, and the derivative is integrable. -/
theorem eulerMaclaurin_firstOrder_finite_Ioc_identity_of_hasDerivAt
    (f f' : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hf_cont : ContinuousOn f
      (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))))
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x)
    (hf'_int : IntegrableOn f'
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)))) :
    (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) =
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) +
        (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
        ((1 / 2 : ℂ) * f (((M : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
  exact
    eulerMaclaurin_firstPeriodicBernoulli_integrationByParts_Ioc
      f f' N M hNM hf_cont hf_deriv hf'_int

/-- Solved-for finite Bernoulli remainder in the first-order Euler-Maclaurin
identity on a natural `Ioc` interval.

This is the finite bounded-primitive integration-by-parts primitive exposed by
the one-interval Bernoulli calculation: the Bernoulli remainder is exactly the
finite endpoint sum minus the main integral and the two half-endpoint terms. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_remainderIntegral_eq_sum_sub_integral_sub_endpoints
    (f f' : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hf_cont : ContinuousOn f
      (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))))
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x)
    (hf'_int : IntegrableOn f'
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)))) :
    (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) =
      (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) -
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) -
        (-(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) -
        ((1 / 2 : ℂ) * f (((M : ℕ) : ℝ))) := by
  let S : ℂ := ∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)
  let I : ℂ := ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x
  let L : ℂ := -(1 / 2 : ℂ) * f (((N : ℕ) : ℝ))
  let U : ℂ := (1 / 2 : ℂ) * f (((M : ℕ) : ℝ))
  let R : ℂ :=
    ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x
  have hem :
      S = I + L + U + R :=
    eulerMaclaurin_firstOrder_finite_Ioc_identity_of_hasDerivAt
      f f' N M hNM hf_cont hf_deriv hf'_int
  have hsolve :
      R = S - I - L - U := by
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
    calc
      R = (I + L + U + R) - I - L - U := hraw.symm
      _ = S - I - L - U := by
        exact congrArg (fun z : ℂ => z - I - L - U) hem.symm
  exact hsolve

/-- Continuity of the zeta complex-power profile on a positive finite real
interval. -/
theorem eulerMaclaurin_cpow_neg_continuousOn_Icc_nat
    (z : ℂ)
    (N M : ℕ)
    (hN : 0 < N) :
    ContinuousOn
      (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-z)))
      (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) := by
  intro x hx
  have hx_pos : 0 < x :=
    lt_of_lt_of_le (Nat.cast_pos.mpr hN) hx.1
  exact
    (Complex.continuousAt_ofReal_cpow_const x (-z)
      (Or.inr (ne_of_gt hx_pos))).continuousWithinAt

/-- Pointwise derivative of the zeta complex-power profile on a positive
finite real interval. -/
theorem eulerMaclaurin_cpow_neg_hasDerivAt_on_Ioo_nat
    (z : ℂ)
    (N M : ℕ)
    (hN : 0 < N) :
    ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
        HasDerivAt
          (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-z)))
          (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))
          x := by
  intro x hx
  have hx_pos : 0 < x :=
    lt_trans (Nat.cast_pos.mpr hN) hx.1
  have hslit : ((x : ℂ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr hx_pos
  have hcomplex :
      HasDerivAt
        (fun w : ℂ => w ^ (-z))
        ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1)
        (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).cpow_const hslit
  have hreal :
      HasDerivAt
        (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-z)))
        ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1)
        x :=
    hcomplex.comp_ofReal
  have hexponent :
      ((-z) - 1) = -(z + 1) := by
    calc
      ((-z) - 1) = (-z) + (-(1 : ℂ)) := by
        exact sub_eq_add_neg (-z) (1 : ℂ)
      _ = -(z + 1) := by
        exact (neg_add z (1 : ℂ)).symm
  have hvalue :
      ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1) =
        -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
    calc
      ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1) =
          (-z) * ((x : ℂ) ^ ((-z) - 1)) := by
        exact mul_one ((-z) * ((x : ℂ) ^ ((-z) - 1)))
      _ = -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
        exact congrArg
          (fun W : ℂ => -z * W)
          (congrArg (fun E : ℂ => ((x : ℂ) ^ E)) hexponent)
  exact hreal.congr_deriv hvalue

/-- Integrability of the derivative profile on a positive finite real
interval. -/
theorem eulerMaclaurin_cpow_neg_derivative_integrableOn_Ioc_nat
    (z : ℂ)
    (N M : ℕ)
    (hN : 0 < N) :
    IntegrableOn
      (fun x : ℝ => -z * (((x : ℝ) : ℂ) ^ (-(z + 1))))
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) := by
  have hcont :
      ContinuousOn
        (fun x : ℝ => -z * (((x : ℝ) : ℂ) ^ (-(z + 1))))
        (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hN) hx.1
    have hcpow_at :
        ContinuousAt
          (fun y : ℝ => (((y : ℝ) : ℂ) ^ (-(z + 1))) )
          x :=
      Complex.continuousAt_ofReal_cpow_const x (-(z + 1))
        (Or.inr (ne_of_gt hx_pos))
    have hmul_at :
        ContinuousAt
          (fun y : ℝ => -z * (((y : ℝ) : ℂ) ^ (-(z + 1))) )
          x :=
      hcpow_at.const_mul (-z)
    exact hmul_at.continuousWithinAt
  have hsubset :
      Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) ⊆
        Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) := by
    intro x hx
    exact ⟨le_of_lt hx.1, hx.2⟩
  exact (ContinuousOn.integrableOn_Icc hcont).mono_set hsubset

/-- Finite first-order Euler-Maclaurin identity for the strict post-cutoff
complex-power tail.

This is the finite owner construction missing from the local file: for
`f(x) = x^{-z}` and positive cutoffs `N ≤ M`, the finite strict tail
`N < n ≤ M` is expressed as the finite integral, the two half-endpoint
corrections, and the first-periodic-Bernoulli derivative remainder.  The
infinite post-cutoff formula below is obtained by sending `M → ∞` in this
identity. -/
theorem eulerMaclaurin_firstOrder_cpow_neg_finite_postCutoffTail_identity_standard
    (z : ℂ)
    (N M : ℕ)
    (hN : 0 < N)
    (hNM : N ≤ M) :
    (∑ n in Finset.Ioc N M, (((n : ℕ) : ℝ) : ℂ) ^ (-z)) =
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        (-(1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) := by
  let f : ℝ → ℂ := fun x : ℝ => (((x : ℝ) : ℂ) ^ (-z))
  let f' : ℝ → ℂ := fun x : ℝ => -z * (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have hf_cont :
      ContinuousOn f
        (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) :=
    eulerMaclaurin_cpow_neg_continuousOn_Icc_nat z N M hN
  have hf_deriv :
      ∀ x : ℝ,
        x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
          HasDerivAt f (f' x) x :=
    eulerMaclaurin_cpow_neg_hasDerivAt_on_Ioo_nat z N M hN
  have hf'_int :
      IntegrableOn f'
        (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) :=
    eulerMaclaurin_cpow_neg_derivative_integrableOn_Ioc_nat z N M hN
  exact
    eulerMaclaurin_firstOrder_finite_Ioc_identity_of_hasDerivAt
      f f' N M hNM hf_cont hf_deriv hf'_int

/-- The upper endpoint correction in the finite post-cutoff complex-power
Euler-Maclaurin identity vanishes as the upper cutoff tends to infinity. -/
theorem eulerMaclaurin_cpow_neg_upperEndpoint_tendsto_zero
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    Tendsto
      (fun M : ℕ => ((1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))))
      atTop
      (𝓝 0) := by
  let f : ℕ → ℂ := fun M : ℕ => (1 : ℂ) / ((M : ℂ) ^ z)
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := z)).mpr hhalf_plane
  have hf_tendsto : Tendsto f atTop (𝓝 0) :=
    hf_summable.tendsto_atTop_zero
  have hterms :
      f =ᶠ[atTop]
        (fun M : ℕ => ((((M : ℕ) : ℝ) : ℂ) ^ (-z))) := by
    exact
      (eventually_gt_atTop (0 : ℕ)).mono
        (fun M hM =>
          have hM_pos : 0 < M :=
            hM
          have hcast : (((M : ℕ) : ℝ) : ℂ) = (M : ℂ) :=
            Complex.ofReal_natCast M
          have hrecip :
              (1 : ℂ) / ((M : ℂ) ^ z) = (M : ℂ) ^ (-z) :=
            eulerMaclaurin_positiveNat_one_div_cpow_eq_cpow_neg z hM_pos
          Eq.trans hrecip (congrArg (fun w : ℂ => w ^ (-z)) hcast.symm))
  have hpow_tendsto :
      Tendsto
        (fun M : ℕ => ((((M : ℕ) : ℝ) : ℂ) ^ (-z)))
        atTop
        (𝓝 0) :=
    hf_tendsto.congr' hterms
  have hmul :
      Tendsto
        (fun M : ℕ => (1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^ (-z)))
        atTop
        (𝓝 ((1 / 2 : ℂ) * 0)) :=
    tendsto_const_nhds.mul hpow_tendsto
  exact
    Eq.subst
      (motive := fun L : ℂ =>
        Tendsto
          (fun M : ℕ => (1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^ (-z)))
          atTop
          (𝓝 L))
      (mul_zero (1 / 2 : ℂ))
      hmul

/-- The finite main integral over `(N, M]` tends to the improper main integral
over `(N, ∞)`. -/
theorem eulerMaclaurin_cpow_neg_integral_Ioc_tendsto_integral_Ioi
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    Tendsto
      (fun M : ℕ =>
        ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z)))
      atTop
      (𝓝
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z)))) := by
  let a : ℝ := ((N : ℕ) : ℝ)
  let f : ℝ → ℂ := fun x : ℝ => (((x : ℝ) : ℂ) ^ (-z))
  have ha_pos : 0 < a := by
    exact Nat.cast_pos.mpr hN
  have hf_int : IntegrableOn f (Set.Ioi a) :=
    integrableOn_Ioi_cpow_of_lt
      (eulerMaclaurin_cpow_neg_re_lt_neg_one_of_one_lt_re hhalf_plane)
      ha_pos
  have h_interval :
      Tendsto
        (fun M : ℕ => ∫ x in a..((M : ℕ) : ℝ), f x)
        atTop
        (𝓝 (∫ x in Set.Ioi a, f x)) :=
    intervalIntegral_tendsto_integral_Ioi
      a hf_int tendsto_natCast_atTop_atTop
  have hset_eq :
      (fun M : ℕ =>
        ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) =ᶠ[atTop]
      (fun M : ℕ => ∫ x in a..((M : ℕ) : ℝ), f x) := by
    exact
      (eventually_ge_atTop N).mono
        (fun M hNM =>
          have hle : a ≤ ((M : ℕ) : ℝ) :=
            Nat.cast_le.mpr hNM
          have hinterval :
              (∫ x in a..((M : ℕ) : ℝ), f x) =
                ∫ x in Set.Ioc a (((M : ℕ) : ℝ)), f x :=
            intervalIntegral.integral_of_le hle
          hinterval.symm)
  exact h_interval.congr' hset_eq.symm

/-- Integrability of the unfactored Bernoulli/cpow kernel on a positive
post-cutoff tail in the convergent half-plane.

The proof is the direct majorant estimate
`|B₁({x}) x^{-(z+1)}| ≤ x^{-(Re z + 1)}` on `x ≥ N ≥ 1`, followed by the
standard real-power tail integrability for exponent below `-1`. -/
theorem eulerMaclaurin_cpow_neg_bernoulliKernel_integrableOn_Ioi
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    IntegrableOn
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(z + 1))))
      (Set.Ioi (((N : ℕ) : ℝ))) := by
  let s : Set ℝ := Set.Ioi (((N : ℕ) : ℝ))
  let f : ℝ → ℂ := fun x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))
  let g : ℝ → ℝ := fun x : ℝ => x ^ (-(z.re + 1))
  have hN_one_nat : 1 ≤ N :=
    Nat.succ_le_of_lt hN
  have hN_one_real : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by
    have hcast : ((1 : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) :=
      Nat.cast_le.mpr hN_one_nat
    exact
      Eq.subst
        (motive := fun t : ℝ => t ≤ ((N : ℕ) : ℝ))
        (Nat.cast_one : ((1 : ℕ) : ℝ) = (1 : ℝ))
        hcast
  have hN_pos_real : 0 < (((N : ℕ) : ℝ)) := by
    exact Nat.cast_pos.mpr hN
  have htwo_le : (2 : ℝ) ≤ z.re + 1 := by
    have hone_le : (1 : ℝ) ≤ z.re :=
      le_of_lt hhalf_plane
    calc
      (2 : ℝ) = 1 + 1 := by
        exact (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
      _ ≤ z.re + 1 :=
        add_le_add hone_le le_rfl
  have hone_lt : (1 : ℝ) < z.re + 1 :=
    lt_of_lt_of_le one_lt_two htwo_le
  have hexponent_lt : -(z.re + 1) < -(1 : ℝ) :=
    neg_lt_neg hone_lt
  have hg_integrable : IntegrableOn g s :=
    integrableOn_Ioi_rpow_of_lt hexponent_lt hN_pos_real
  have hf_meas :
      AEStronglyMeasurable f (volume.restrict s) := by
    exact
      (eulerMaclaurinBernoulliKernel_aestronglyMeasurable N hN z)
  have hbound :
      ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x := by
    exact (ae_restrict_mem measurableSet_Ioi).mono
      (fun x hx_tail => by
        have hx_one : 1 ≤ x :=
          le_trans hN_one_real (le_of_lt hx_tail)
        have hx_pos : 0 < x :=
          lt_of_lt_of_le zero_lt_one hx_one
        have hB :
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 :=
          eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_local x
        have hcpow :
            ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ g x :=
          eulerMaclaurin_norm_real_cpow_le_rpow_of_re_lower
            (δ := z.re) hx_pos hx_one z le_rfl
        have hmul :
            ‖f x‖ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ := by
          exact norm_mul
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
            (((x : ℝ) : ℂ) ^ (-(z + 1)))
        have hproduct :
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤
              1 * g x :=
          mul_le_mul hB hcpow
            (norm_nonneg (((x : ℝ) : ℂ) ^ (-(z + 1))))
            (zero_le_one : (0 : ℝ) ≤ 1)
        calc
          ‖f x‖ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ :=
            hmul
          _ ≤ 1 * g x :=
            hproduct
          _ = g x :=
            one_mul (g x))
  exact Integrable.mono' hg_integrable hf_meas hbound

/-- Integrability of the first-order Bernoulli derivative remainder tail in
the convergent zeta half-plane. -/
theorem eulerMaclaurin_cpow_neg_bernoulliRemainder_integrableOn_Ioi
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    IntegrableOn
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))
      (Set.Ioi (((N : ℕ) : ℝ))) := by
  let f : ℝ → ℂ := fun x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have hf_int : IntegrableOn f (Set.Ioi (((N : ℕ) : ℝ))) :=
    eulerMaclaurin_cpow_neg_bernoulliKernel_integrableOn_Ioi
      z N hN hhalf_plane
  have hpoint_on :
      EqOn
        (fun x : ℝ => -z * f x)
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))
        (Set.Ioi (((N : ℕ) : ℝ))) := by
    intro x _hx
    exact
      (by
        let a : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
        let b : ℂ := (((x : ℝ) : ℂ) ^ (-(z + 1)))
        calc
          -z * (a * b) = (-z * a) * b := by
            exact (mul_assoc (-z) a b).symm
          _ = (a * -z) * b := by
            exact congrArg (fun y : ℂ => y * b) (mul_comm (-z) a)
          _ = a * (-z * b) := by
            exact mul_assoc a (-z) b)
  have hconst :
      IntegrableOn
        (fun x : ℝ => -z * f x)
        (Set.Ioi (((N : ℕ) : ℝ))) :=
    hf_int.const_mul (-z)
  exact hconst.congr_fun hpoint_on measurableSet_Ioi

/-- The finite Bernoulli remainder integral over `(N, M]` tends to the
improper Bernoulli remainder integral over `(N, ∞)`. -/
theorem eulerMaclaurin_cpow_neg_bernoulliRemainder_Ioc_tendsto_integral_Ioi
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    Tendsto
      (fun M : ℕ =>
        ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))
      atTop
      (𝓝
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  let a : ℝ := ((N : ℕ) : ℝ)
  let f : ℝ → ℂ := fun x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))
  have hf_int : IntegrableOn f (Set.Ioi a) :=
    eulerMaclaurin_cpow_neg_bernoulliRemainder_integrableOn_Ioi
      z N hN hhalf_plane
  have h_interval :
      Tendsto
        (fun M : ℕ => ∫ x in a..((M : ℕ) : ℝ), f x)
        atTop
        (𝓝 (∫ x in Set.Ioi a, f x)) :=
    intervalIntegral_tendsto_integral_Ioi
      a hf_int tendsto_natCast_atTop_atTop
  have hset_eq :
      (fun M : ℕ =>
        ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =ᶠ[atTop]
      (fun M : ℕ => ∫ x in a..((M : ℕ) : ℝ), f x) := by
    exact
      (eventually_ge_atTop N).mono
        (fun M hNM =>
          have hle : a ≤ ((M : ℕ) : ℝ) :=
            Nat.cast_le.mpr hNM
          have hinterval :
              (∫ x in a..((M : ℕ) : ℝ), f x) =
                ∫ x in Set.Ioc a (((M : ℕ) : ℝ)), f x :=
            intervalIntegral.integral_of_le hle
          hinterval.symm)
  exact h_interval.congr' hset_eq.symm

/-- Range partial sums of a zero-extended strict tail are the corresponding
`Ioc` sums. -/
theorem sum_range_succ_strictTail_eq_sum_Ioc
    (f : ℕ → ℂ)
    (N M : ℕ) :
    (∑ n in Finset.range (M + 1), if N < n then f n else 0) =
      ∑ n in Finset.Ioc N M, f n := by
  calc
    (∑ n in Finset.range (M + 1), if N < n then f n else 0) =
        ∑ n in (Finset.range (M + 1)).filter (fun n : ℕ => N < n), f n := by
      exact (Finset.sum_filter (s := Finset.range (M + 1))
        (p := fun n : ℕ => N < n) (f := f)).symm
    _ = ∑ n in Finset.Ioc N M, f n := by
      have hset :
          (Finset.range (M + 1)).filter (fun n : ℕ => N < n) =
            Finset.Ioc N M := by
        ext n
        constructor
        · intro hn
          have hn_range : n ∈ Finset.range (M + 1) :=
            (Finset.mem_filter.mp hn).1
          have hn_gt : N < n :=
            (Finset.mem_filter.mp hn).2
          have hn_le : n ≤ M :=
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hn_range)
          exact Finset.mem_Ioc.mpr ⟨hn_gt, hn_le⟩
        · intro hn
          have hn_gt : N < n :=
            (Finset.mem_Ioc.mp hn).1
          have hn_le : n ≤ M :=
            (Finset.mem_Ioc.mp hn).2
          have hn_range : n ∈ Finset.range (M + 1) :=
            Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn_le)
          exact Finset.mem_filter.mpr ⟨hn_range, hn_gt⟩
      exact congrArg (fun s : Finset ℕ => ∑ n in s, f n) hset

/-- Ordered finite strict-tail sums over `Ioc N M` give the unconditional
`HasSum` of the zero-extended post-cutoff sequence once the latter is
absolutely summable.

This is the index bridge between the sequential Euler-Maclaurin finite-window
limit and mathlib's unordered `HasSum` over `ℕ`. -/
theorem hasSum_of_Ioc_strictTail_tendsto_of_summable_norm
    (f : ℕ → ℂ)
    (N : ℕ)
    (S : ℂ)
    (hsummable_norm : Summable
      (fun n : ℕ => ‖if N < n then f n else 0‖))
    (htendsto :
      Tendsto
        (fun M : ℕ => ∑ n in Finset.Ioc N M, f n)
        atTop
        (𝓝 S)) :
    HasSum
      (fun n : ℕ => if N < n then f n else 0)
      S := by
  let g : ℕ → ℂ := fun n : ℕ => if N < n then f n else 0
  have hshift :
      Tendsto
        (fun M : ℕ => ∑ n in Finset.range (M + 1), g n)
        atTop
        (𝓝 S) := by
    have hpoint :
        (fun M : ℕ => ∑ n in Finset.range (M + 1), g n) =ᶠ[atTop]
        (fun M : ℕ => ∑ n in Finset.Ioc N M, f n) :=
      Filter.Eventually.of_forall
        (fun M : ℕ => sum_range_succ_strictTail_eq_sum_Ioc f N M)
    exact htendsto.congr' hpoint.symm
  have hunshift :
      Tendsto
        (fun M : ℕ => ∑ n in Finset.range M, g n)
        atTop
        (𝓝 S) := by
    exact (tendsto_add_atTop_iff_nat (f :=
      fun M : ℕ => ∑ n in Finset.range M, g n) 1).mp hshift
  have hhas :
      HasSum g S :=
    (hasSum_iff_tendsto_nat_of_summable_norm hsummable_norm).mpr
      hunshift
  exact hhas

/-- Limit passage from the finite strict-tail Euler-Maclaurin identity to the
improper post-cutoff `HasSum`.

The analytic inputs are exactly the finite identity above, decay in the
half-plane `1 < Re z`, and integrability of the Bernoulli derivative tail. -/
theorem eulerMaclaurin_firstOrder_cpow_neg_finite_postCutoffTail_tendsto_hasSum
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        (-(1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  have hfinite :
      ∀ M : ℕ, N ≤ M →
        (∑ n in Finset.Ioc N M, (((n : ℕ) : ℝ) : ℂ) ^ (-z)) =
          (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              (((x : ℝ) : ℂ) ^ (-z))) +
            (-(1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
            ((1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))) +
            (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) := by
    intro M hNM
    exact
      eulerMaclaurin_firstOrder_cpow_neg_finite_postCutoffTail_identity_standard
        z N M hN hNM
  have hendpoint :
      Tendsto
        (fun M : ℕ => ((1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))))
        atTop
        (𝓝 0) :=
    eulerMaclaurin_cpow_neg_upperEndpoint_tendsto_zero z hhalf_plane
  have hmain :
      Tendsto
        (fun M : ℕ =>
          ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z)))
        atTop
        (𝓝
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z)))) :=
    eulerMaclaurin_cpow_neg_integral_Ioc_tendsto_integral_Ioi
      z N hN hhalf_plane
  have hremainder :
      Tendsto
        (fun M : ℕ =>
          ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))
        atTop
        (𝓝
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) :=
    eulerMaclaurin_cpow_neg_bernoulliRemainder_Ioc_tendsto_integral_Ioi
      z N hN hhalf_plane
  let A : ℂ :=
    ∫ x in Set.Ioi (((N : ℕ) : ℝ)),
      (((x : ℝ) : ℂ) ^ (-z))
  let B : ℂ :=
    -(1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))
  let C : ℂ :=
    ∫ x in Set.Ioi (((N : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))
  have hfinite_tendsto :
      Tendsto
        (fun M : ℕ =>
          ∑ n in Finset.Ioc N M, (((n : ℕ) : ℝ) : ℂ) ^ (-z))
        atTop
        (𝓝 (A + B + C)) := by
    have hfinite_eventually :
        (fun M : ℕ =>
          ∑ n in Finset.Ioc N M, (((n : ℕ) : ℝ) : ℂ) ^ (-z))
          =ᶠ[atTop]
        (fun M : ℕ =>
          (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z))) +
            B +
            ((1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))) +
            (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
      exact
        (eventually_ge_atTop N).mono
          (fun M hNM => hfinite M hNM)
    have hassembled :
        Tendsto
          (fun M : ℕ =>
            (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                (((x : ℝ) : ℂ) ^ (-z))) +
              B +
              ((1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))) +
              (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))))
          atTop
          (𝓝 (A + B + 0 + C)) := by
      exact
        (((hmain.add tendsto_const_nhds).add hendpoint).add hremainder)
    have htarget_base : (A + B) + 0 = A + B :=
      add_zero (A + B)
    have htarget : A + B + 0 + C = A + B + C :=
      congrArg (fun x : ℂ => x + C) htarget_base
    have hsum_tendsto_grouped :
        Tendsto
          (fun M : ℕ =>
            ∑ n in Finset.Ioc N M,
              (((n : ℕ) : ℝ) : ℂ) ^ (-z))
          atTop
          (𝓝 (A + B + 0 + C)) :=
      hassembled.congr' hfinite_eventually.symm
    exact
      Eq.subst
        (motive := fun T : ℂ =>
          Tendsto
            (fun M : ℕ =>
              ∑ n in Finset.Ioc N M,
                (((n : ℕ) : ℝ) : ℂ) ^ (-z))
            atTop
            (𝓝 T))
        htarget
        hsum_tendsto_grouped
  have hsummable_tail :
      Summable
        (fun n : ℕ =>
          if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) := by
    have hone_div_summable :
        Summable
          (fun n : ℕ =>
            if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) := by
      let f : ℕ → ℂ := fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ z)
      have hf_summable : Summable f :=
        (Complex.summable_one_div_nat_cpow (p := z)).mpr hhalf_plane
      have hindicator_summable :
          Summable ({n : ℕ | N < n}.indicator f) :=
        hf_summable.indicator (fun n : ℕ => N < n)
      have hindicator_pointwise :
          ∀ n : ℕ,
            ({m : ℕ | N < m}.indicator f) n =
              if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0 :=
        fun n : ℕ => Set.indicator_apply {m : ℕ | N < m} f n
      exact hindicator_summable.congr hindicator_pointwise
    have hterms :
        (fun n : ℕ =>
          if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
        (fun n : ℕ =>
          if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) :=
      eulerMaclaurin_cpow_neg_postCutoffTail_terms_eq_one_div z N hN
    exact Eq.subst
      (motive := fun F : ℕ → ℂ => Summable F)
      hterms.symm
      hone_div_summable
  have hsummable_norm :
      Summable
        (fun n : ℕ =>
          ‖if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0‖) :=
    summable_norm_iff.mpr hsummable_tail
  exact
    hasSum_of_Ioc_strictTail_tendsto_of_summable_norm
      (fun n : ℕ => (((n : ℕ) : ℝ) : ℂ) ^ (-z))
      N
      (A + B + C)
      hsummable_norm
      hfinite_tendsto

/-- Standard first-order Euler-Maclaurin formula for the zeta complex-power
post-cutoff tail in function notation.

The earlier arbitrary-function version of this statement is false without
decay and integrability hypotheses.  The owner statement here is the actual
zeta specialization used downstream: for `1 < Re z`, the function
`x ↦ x^{-z}` has enough decay for the infinite first-order
Euler-Maclaurin formula. -/
theorem eulerMaclaurin_firstOrder_postCutoffTail_hasSum_standard
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        (-(1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  exact
    eulerMaclaurin_firstOrder_cpow_neg_finite_postCutoffTail_tendsto_hasSum
      z N hN hhalf_plane

/-- Specialization of the first-order Euler-Maclaurin theorem to
`f(x)=x^{-z}` in function notation. -/
theorem eulerMaclaurin_cpow_neg_postCutoffTail_function_hasSum_standard
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        (-(1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  exact
    eulerMaclaurin_firstOrder_postCutoffTail_hasSum_standard
      z N hN hhalf_plane

/-- Fold the derivative into the periodic-Bernoulli integral for
`f(x)=x^{-z}`. -/
theorem eulerMaclaurin_cpow_neg_derivative_integral_eq_factored_remainder
    (z : ℂ)
    (N : ℕ) :
    (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
      -z *
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((x : ℝ) : ℂ) ^ (-(z + 1)))) := by
  let g : ℝ → ℂ := fun x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have hpoint_on :
      EqOn
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))
        (fun x : ℝ => -z * g x)
        (Set.Ioi (((N : ℕ) : ℝ))) := by
    intro x _hx
    exact
      (by
        let a : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
        let b : ℂ := (((x : ℝ) : ℂ) ^ (-(z + 1)))
        calc
          a * (-z * b) = (a * -z) * b := by
            exact (mul_assoc a (-z) b).symm
          _ = (-z * a) * b := by
            exact congrArg (fun w : ℂ => w * b) (mul_comm a (-z))
          _ = -z * (a * b) := by
            exact mul_assoc (-z) a b)
  have hintegral_point :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
        ∫ x in Set.Ioi (((N : ℕ) : ℝ)), -z * g x := by
    exact setIntegral_congr_fun measurableSet_Ioi hpoint_on
  have hlinear :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)), -z * g x) =
        -z *
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)), g x) := by
    exact integral_mul_left (-z) g
  exact Eq.trans hintegral_point hlinear

/-- The strict post-cutoff Dirichlet term used by the standard tail formula. -/
def eulerMaclaurin_cpow_neg_postCutoffTail_term
    (z : ℂ)
    (N n : ℕ) : ℂ :=
  if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0

/-- Main improper integral in the standard post-cutoff tail formula. -/
def eulerMaclaurin_cpow_neg_postCutoffTail_main
    (z : ℂ)
    (N : ℕ) : ℂ :=
  ∫ x in Set.Ioi (((N : ℕ) : ℝ)), (((x : ℝ) : ℂ) ^ (-z))

/-- Endpoint correction in the standard post-cutoff tail formula. -/
def eulerMaclaurin_cpow_neg_postCutoffTail_endpoint
    (z : ℂ)
    (N : ℕ) : ℂ :=
  -(1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))

/-- Bernoulli remainder integral before multiplication by `-z`. -/
def eulerMaclaurin_cpow_neg_postCutoffTail_remainderIntegral
    (z : ℂ)
    (N : ℕ) : ℂ :=
  ∫ x in Set.Ioi (((N : ℕ) : ℝ)),
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))

/-- Target value in the standard post-cutoff tail formula. -/
def eulerMaclaurin_cpow_neg_postCutoffTail_target
    (z : ℂ)
    (N : ℕ) : ℂ :=
  eulerMaclaurin_cpow_neg_postCutoffTail_main z N +
    eulerMaclaurin_cpow_neg_postCutoffTail_endpoint z N +
    (-z * eulerMaclaurin_cpow_neg_postCutoffTail_remainderIntegral z N)

end
end LFunctions
end Boundary
