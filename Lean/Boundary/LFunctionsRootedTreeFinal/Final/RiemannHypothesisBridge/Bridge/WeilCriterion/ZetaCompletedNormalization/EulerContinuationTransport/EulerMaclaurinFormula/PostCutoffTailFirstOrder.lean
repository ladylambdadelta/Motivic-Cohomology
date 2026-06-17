import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PostCutoffTail

/-!
# Euler-Maclaurin post-cutoff first-order wrapper

This file owns the final conversion from the function-form post-cutoff
Euler-Maclaurin theorem to the standard Dirichlet-tail formula.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Filter MeasureTheory Set

/-- Generic first-order Euler-Maclaurin formula for the infinite post-cutoff
tail of `x ↦ x^{-z}`.

For any positive natural cutoff `N` and `1 < Re z`, the Dirichlet tail after
`N` has sum equal to the improper integral, the endpoint correction, and the
periodic Bernoulli derivative remainder.  This is the canonical non-zeta
Euler-Maclaurin owner theorem consumed by the zeta cutoff specialization. -/
theorem eulerMaclaurin_cpow_neg_postCutoffTail_firstOrder_hasSum_standard
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        (-(1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) +
        (-z *
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  have hfunction :
      HasSum
        (fun n : ℕ =>
          if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
        ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z))) +
          (-(1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) :=
    eulerMaclaurin_cpow_neg_postCutoffTail_function_hasSum_standard
      z N hN hhalf_plane
  have hterm_eq :
      ∀ n : ℕ,
        (fun k : ℕ =>
          if N < k then
            (1 : ℂ) / ((k : ℂ) ^ z)
          else
            0) n =
        (fun k : ℕ =>
          if N < k then (((k : ℕ) : ℝ) : ℂ) ^ (-z) else 0) n := by
    intro n
    have hterm_function :
        (fun k : ℕ =>
          if N < k then (((k : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
        (fun k : ℕ =>
          if N < k then
            (1 : ℂ) / ((k : ℂ) ^ z)
          else
            0) :=
      eulerMaclaurin_cpow_neg_postCutoffTail_terms_eq_one_div z N hN
    exact congrFun hterm_function.symm n
  have hseq_changed :
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z))) +
          (-(1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) :=
    hfunction.congr_fun hterm_eq
  have hsum_eq :
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        (-(1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) =
        ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        (-(1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) +
        (-z *
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
    have hendpoint :
        (-(1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) =
          (-(1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) := by
      have hcast : (((N : ℕ) : ℝ) : ℂ) = (N : ℂ) :=
        Complex.ofReal_natCast N
      have hpow :
          ((((N : ℕ) : ℝ) : ℂ) ^ (-z)) =
            (N : ℂ) ^ (-z) :=
        congrArg (fun w : ℂ => w ^ (-z)) hcast
      have hrecip :
          (1 : ℂ) / ((N : ℂ) ^ z) = (N : ℂ) ^ (-z) :=
        eulerMaclaurin_positiveNat_one_div_cpow_eq_cpow_neg z hN
      exact congrArg (fun W : ℂ => -(1 / 2 : ℂ) * W)
        (Eq.trans hpow hrecip.symm)
    have hremainder :
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
          -z *
            (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1)))) :=
      eulerMaclaurin_cpow_neg_derivative_integral_eq_factored_remainder z N
    exact congrArg₂
      (fun A B : ℂ =>
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) + A + B)
      hendpoint
      hremainder
  exact Eq.subst
    (motive := fun target : ℂ =>
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        target)
    hsum_eq
    hseq_changed

end
end LFunctions
end Boundary
