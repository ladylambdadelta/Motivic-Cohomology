import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.BernoulliCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.HalfPlaneTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.FixedCutoffHolomorphic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PostCutoffTailFirstOrder

/-!
# Euler-Maclaurin zeta tail identities

This file owns the post-cutoff/fixed-cutoff tail-sum identities and their
conversion into the global raw first-order Euler-Maclaurin formula.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Filter MeasureTheory Set
local notation "π" => Real.pi

/-- Specialization of the generic Euler-Maclaurin tail formula to the owner
cutoff `⌊2 + ‖z‖⌋₊`, before folding the Bernoulli integral into the named core. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_unfolded_hasSum
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (((∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        (-(1 / 2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))) +
        (-z *
          (∫ x in Set.Ioi
            (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1))))))) := by
  exact
    eulerMaclaurin_cpow_neg_postCutoffTail_firstOrder_hasSum_standard
      z
      (eulerMaclaurinPoleClearedZetaCutoff z)
      (eulerMaclaurinPoleClearedZetaCutoff_pos z)
      hhalf_plane

/-- Standard first-order Euler-Maclaurin formula for the convergent
post-cutoff Dirichlet tail of `x ↦ x^{-z}`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_hasSum_standard
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (((∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        (-(1 / 2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))) +
        (-z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z))) := by
  exact
    eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_unfolded_hasSum
      z hhalf_plane

/-- Transport the standard first-order Euler-Maclaurin tail formula into the
raw owner terms `MainTerm`, `EndpointTerm`, and
`BernoulliIntegralRemainder`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_ownerTerms_hasSum
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z) := by
  have hstandard :
      HasSum
        (fun n : ℕ =>
          if eulerMaclaurinPoleClearedZetaCutoff z < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (((∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z))) +
          (-(1 / 2 : ℂ) *
            (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))) +
          (-z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z))) :=
    eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_hasSum_standard
      z hhalf_plane
  have hmain :
      (∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) =
        eulerMaclaurinZetaMainTerm z :=
    eulerMaclaurin_riemannZeta_postCutoffTail_integralMain_eq_mainTerm_standard
      z hhalf_plane
  have hendpoint :
      (-(1 / 2 : ℂ)) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) =
        eulerMaclaurinZetaEndpointTerm z :=
    eulerMaclaurin_riemannZeta_postCutoffTail_endpoint_eq_endpointTerm z
  have hremainder :
      -z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z =
        eulerMaclaurinZetaBernoulliIntegralRemainder z :=
    eulerMaclaurin_riemannZeta_postCutoffTail_remainderSign_eq_remainderTerm z
  have howner_sum :
      ((∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        (-(1 / 2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))) +
        (-z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z)) =
        eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z := by
    exact
      congrArg₂
        (fun left right : ℂ => left + right)
        (congrArg₂
          (fun left right : ℂ => left + right)
          hmain
          hendpoint)
        hremainder
  exact
    Eq.subst
      (motive := fun ownerSum : ℂ =>
        HasSum
          (fun n : ℕ =>
            if eulerMaclaurinPoleClearedZetaCutoff z < n then
              (1 : ℂ) / ((n : ℂ) ^ z)
            else
              0)
          ownerSum)
      howner_sum
      hstandard

/-- The height-dependent owner defect agrees pointwise with the fixed-cutoff
defect at the cutoff chosen by that point. -/
theorem eulerMaclaurin_riemannZeta_tailIdentityDefect_eq_fixedCutoffDefect
    (z : ℂ) :
    eulerMaclaurin_riemannZeta_tailIdentityDefect z =
      eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
        (eulerMaclaurinPoleClearedZetaCutoff z) z := by
  rfl

/-- In the convergent half-plane, removing a fixed finite Dirichlet window from
`ζ(s)` leaves the fixed post-cutoff Dirichlet tail as a `HasSum`. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoff_halfPlane_finite_split_tail_hasSum
    (N : ℕ)
    (z : ℂ)
    (hz : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z) := by
  let f : ℕ → ℂ := fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ z)
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := z)).mpr hz
  have hζ_eq : riemannZeta z = ∑' n : ℕ, f n :=
    zeta_eq_tsum_one_div_nat_cpow hz
  have hf_has_tsum : HasSum f (∑' n : ℕ, f n) :=
    hf_summable.hasSum
  have hf_has_zeta : HasSum f (riemannZeta z) :=
    Eq.subst
      (motive := fun S : ℂ => HasSum f S)
      hζ_eq.symm
      hf_has_tsum
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} => f x)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hf_has_zeta
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := f)).mp
        htail_compl
  have hf_zero : f 0 = 0 := by
    calc
      f 0 = (1 : ℂ) / (((0 : ℕ) : ℂ) ^ z) := rfl
      _ = 0 := by
        have hzero : (((0 : ℕ) : ℂ) = (0 : ℂ)) :=
          Nat.cast_zero
        exact Eq.subst
          (motive := fun w : ℂ => (1 : ℂ) / (w ^ z) = 0)
          hzero.symm
          (riemannZeta_dirichletTerm_zero_of_one_lt_re hz)
  have hindicator_point :
      ∀ n : ℕ,
        (if N < n then f n else 0) =
          ({k : ℕ | k ∉ Finset.Icc 1 N}.indicator f) n :=
    fun n : ℕ =>
      (nat_not_Icc_one_indicator_eq_cutoff_if_of_zero f N n hf_zero).symm
  have htail_if :
      HasSum
        (fun k : ℕ => if N < k then f k else 0)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    htail_indicator.congr_fun hindicator_point
  exact htail_if

/-- Fixed-cutoff integral main term in owner normalization. -/
theorem eulerMaclaurin_fixedCutoff_integralMain_eq_mainTerm
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-z))) =
      eulerMaclaurinZetaMainTermWithCutoff N z := by
  have hformula :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) =
        -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) := by
    exact
      integral_Ioi_cpow_of_lt
        (eulerMaclaurin_cpow_neg_re_lt_neg_one_of_one_lt_re hhalf_plane)
        (Nat.cast_pos.mpr hN)
  let A : ℂ := ((N : ℕ) : ℂ)
  have hbase :
      (((N : ℕ) : ℝ) : ℂ) = A :=
    Complex.ofReal_natCast N
  have hexponent :
      (-z) + 1 = (1 : ℂ) - z := by
    calc
      (-z) + 1 = (1 : ℂ) + (-z) := by
        exact add_comm (-z) (1 : ℂ)
      _ = (1 : ℂ) - z := by
        exact (sub_eq_add_neg (1 : ℂ) z).symm
  have hden :
      (-z) + 1 = -((z - 1)) := by
    calc
      (-z) + 1 = (1 : ℂ) - z :=
        hexponent
      _ = -(z - 1) := by
        exact (neg_sub z (1 : ℂ)).symm
  have hpow :
      ((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) =
        A ^ ((1 : ℂ) - z) := by
    exact congrArg₂ (fun b e : ℂ => b ^ e) hbase hexponent
  have hnormal :
      -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) =
        A ^ ((1 : ℂ) - z) / (z - 1) := by
    calc
      -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) =
          -(A ^ ((1 : ℂ) - z)) / ((-z) + 1) := by
        exact congrArg
          (fun W : ℂ => -W / ((-z) + 1))
          hpow
      _ = -(A ^ ((1 : ℂ) - z)) / (-(z - 1)) := by
        exact congrArg
          (fun D : ℂ => -(A ^ ((1 : ℂ) - z)) / D)
          hden
      _ = A ^ ((1 : ℂ) - z) / (z - 1) := by
        exact neg_div_neg_eq (A ^ ((1 : ℂ) - z)) (z - 1)
  exact Eq.trans hformula hnormal

/-- Fixed-cutoff Euler-Maclaurin tail formula in owner term notation. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoff_postCutoffTail_ownerTerms_hasSum
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (eulerMaclaurinZetaMainTermWithCutoff N z +
        eulerMaclaurinZetaEndpointTermWithCutoff N z +
        eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z) := by
  have hstandard :
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
                (((x : ℝ) : ℂ) ^ (-(z + 1)))))) :=
    eulerMaclaurin_cpow_neg_postCutoffTail_firstOrder_hasSum_standard
      z N hN hhalf_plane
  have hmain :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z)) ) =
        eulerMaclaurinZetaMainTermWithCutoff N z :=
    eulerMaclaurin_fixedCutoff_integralMain_eq_mainTerm N hN z hhalf_plane
  have hendpoint :
      (-(1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) =
        eulerMaclaurinZetaEndpointTermWithCutoff N z := by
    rfl
  have hremainder :
      (-z *
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
        eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z := by
    rfl
  have hsum_eq :
      (((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
          (-(1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) +
          (-z *
            (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1))))))) =
        eulerMaclaurinZetaMainTermWithCutoff N z +
          eulerMaclaurinZetaEndpointTermWithCutoff N z +
          eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z := by
    exact congrArg₂
      (fun A B : ℂ => A + B)
          (congrArg₂
            (fun A B : ℂ => A + B)
            hmain
            hendpoint)
          hremainder
  exact
    Eq.subst
      (motive := fun S : ℂ =>
        HasSum
          (fun n : ℕ =>
            if N < n then
              (1 : ℂ) / ((n : ℂ) ^ z)
            else
              0)
          S)
      hsum_eq
      hstandard

/-- Vanishing of the Euler-Maclaurin tail defect is exactly the desired
tail identity. -/
theorem eulerMaclaurin_riemannZeta_tailIdentity_of_defect_eq_zero
    {z : ℂ}
    (hdefect : eulerMaclaurin_riemannZeta_tailIdentityDefect z = 0) :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
      eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  exact sub_eq_zero.mp hdefect

/-- In the convergent half-plane, the Euler-Maclaurin tail defect vanishes by
uniqueness of the post-cutoff `HasSum`: the Dirichlet split and the
Euler-Maclaurin tail formula have the same summand. -/
theorem eulerMaclaurin_riemannZeta_tailIdentityDefect_eq_zero_on_halfPlane
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    eulerMaclaurin_riemannZeta_tailIdentityDefect z = 0 := by
  have hsplit :
      HasSum
        (fun n : ℕ =>
          if eulerMaclaurinPoleClearedZetaCutoff z < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (riemannZeta z - eulerMaclaurinZetaFinitePart z) :=
    eulerMaclaurin_riemannZeta_halfPlane_finite_split_tail_hasSum
      z hhalf_plane
  have htail :
      HasSum
        (fun n : ℕ =>
          if eulerMaclaurinPoleClearedZetaCutoff z < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
    eulerMaclaurin_riemannZeta_postCutoffTail_ownerTerms_hasSum
      z hhalf_plane
  have hidentity :
      riemannZeta z - eulerMaclaurinZetaFinitePart z =
        eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z :=
    hsplit.unique htail
  exact sub_eq_zero.mpr hidentity

/-- First-order Euler-Maclaurin evaluation of the convergent post-cutoff
Dirichlet tail. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_eulerMaclaurin_hasSum_standard
    (z : ℂ)
    (_hz_one : 1 ≤ z.re)
    (_hz_two : z.re ≤ 2)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z) := by
  exact
    eulerMaclaurin_riemannZeta_postCutoffTail_ownerTerms_hasSum
      z hhalf_plane

end
end LFunctions
end Boundary
