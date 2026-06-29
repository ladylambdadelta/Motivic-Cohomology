import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroMultiplicityCore.RadialGap.Owner

/-!
# Jensen finite-support zero divisor core

This owner layer was split from `ZeroMultiplicityCore.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

/-- Adding back the single origin summand preserves closed-disk summability. -/
theorem entireFunctionZeroMultiplicityClosedDiskSummand_eq_nonzero_add_origin_pointwise
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    (z : EntireFunctionZero F) :
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z =
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z +
        entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z :=
  entireFunctionZeroMultiplicityClosedDiskSummand_eq_nonzero_add_origin F hF R z

theorem entireFunctionZeroMultiplicityClosedDiskSummable_of_nonzeroClosedDiskSummable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    [Decidable (F 0 = 0)]
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)]
    [DecidableEq (EntireFunctionZero F)]
    (hclosed :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) := by
  have horigin_summable :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) :=
    entireFunctionOriginZeroMultiplicityClosedDiskSummable F hF R
  exact
    (hclosed.add horigin_summable).congr
      (fun z => by
        exact (entireFunctionZeroMultiplicityClosedDiskSummand_eq_nonzero_add_origin_pointwise
          F hF z).symm)

/-- The zero set of a nontrivial entire function inside a closed disk is
discrete. -/
theorem entireFunction_closedDiskZeros_discreteTopology
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ) :
    DiscreteTopology {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} := by
  exact
    (discreteTopology_subtype_iff).2
      (fun x hx =>
      have _hxzero : F x = 0 := hx.2
      have hne : ∀ᶠ w in 𝓝[≠] x, F w ≠ 0 := by
        match (hF x).eventually_eq_zero_or_eventually_ne_zero with
        | Or.inl hzero =>
            have hU : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) := fun z _ => hF z
            have hEq : EqOn F 0 (Set.univ : Set ℂ) :=
              hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero
                isPreconnected_univ (by exact mem_univ _) hzero
            exact
              False.elim
                (Exists.elim hnontrivial
                  (fun z0 hz0 => hz0 (hEq (by exact mem_univ _))))
        | Or.inr hne => exact hne
      have hScompl :
          ({z : ℂ | ‖z‖ ≤ R ∧ F z = 0}ᶜ) ∈ 𝓝[≠] x := by
        exact
          Filter.mem_of_superset hne
            (fun w hw hsw => hw hsw.2)
      (Filter.disjoint_principal_right.2 hScompl).eq_bot)

/-- A nontrivial entire function has only finitely many zeros in each closed
disk. -/
theorem entireFunction_closedDiskZeros_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ) :
    Set.Finite {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} := by
  have hdisc :
      DiscreteTopology {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} :=
    entireFunction_closedDiskZeros_discreteTopology F hF hnontrivial R
  have hclosedDisk : IsClosed {z : ℂ | ‖z‖ ≤ R} := by
    change IsClosed ((fun z : ℂ => ‖z‖) ⁻¹' Set.Iic R)
    exact IsClosed.preimage (continuous_norm : Continuous fun z : ℂ => ‖z‖) isClosed_Iic
  have hzeroClosed : IsClosed {z : ℂ | F z = 0} := by
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    change IsClosed (F ⁻¹' ({0} : Set ℂ))
    exact IsClosed.preimage hcontF (isClosed_singleton : IsClosed ({0} : Set ℂ))
  have hclosed : IsClosed {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} := by
    change IsClosed ({z : ℂ | ‖z‖ ≤ R} ∩ {z : ℂ | F z = 0})
    exact hclosedDisk.inter hzeroClosed
  have hsubset :
      {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    have hdist : dist z 0 = ‖(z : ℂ)‖ := by
      calc
        dist z 0 = ‖z - 0‖ := dist_eq_norm z 0
        _ = ‖(z : ℂ)‖ := by
          exact congrArg norm (sub_zero z)
    have hle : ‖(z : ℂ)‖ ≤ R := hz.1
    calc
      dist z 0 = ‖(z : ℂ)‖ := hdist
      _ ≤ R := hle
  have hcomp : IsCompact {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hclosed hsubset
  haveI : DiscreteTopology {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} := hdisc
  exact finite_coe_iff.mp
    (@finite_of_compact_of_discrete
      {z : ℂ | ‖z‖ ≤ R ∧ F z = 0}
      _ (isCompact_iff_compactSpace.mp hcomp) inferInstance)

/-- The nonzero closed-disk multiplicity summand has finite support. -/
theorem entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (R : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)] :
    (Function.support
      (fun z : EntireFunctionZero F =>
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)).Finite := by
  have hzeros :
      Set.Finite {w : ℂ | ‖w‖ ≤ R ∧ F w = 0} :=
    entireFunction_closedDiskZeros_finite F hF ⟨0, hF0⟩ R
  have hpre :
      ((fun z : EntireFunctionZero F => (z : ℂ)) ⁻¹'
        {w : ℂ | ‖w‖ ≤ R ∧ F w = 0}).Finite :=
    hzeros.preimage (fun _ _ _ _ hEq => Subtype.ext hEq)
  exact hpre.subset (by
    intro z hz
    have hne :
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z ≠ 0 := by
      intro hzero
      exact hz hzero
    have hlt :
        ‖(z : ℂ)‖ ≤ R :=
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_subset_closedDisk
        F hF z hne
    exact ⟨hlt, z.2⟩)

/-- The Jensen radial-gap summand has finite support. -/
theorem entireFunctionJensenRadialGapSummand_support_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)] :
    (Function.support
      (fun z : EntireFunctionZero F =>
        entireFunctionJensenRadialGapSummand F hF ρ z)).Finite := by
  have hzeros :
      Set.Finite {w : ℂ | ‖w‖ ≤ ρ ∧ F w = 0} :=
    entireFunction_closedDiskZeros_finite F hF ⟨0, hF0⟩ ρ
  have hpre :
      ((fun z : EntireFunctionZero F => (z : ℂ)) ⁻¹'
        {w : ℂ | ‖w‖ ≤ ρ ∧ F w = 0}).Finite :=
    hzeros.preimage (fun _ _ _ _ hEq => Subtype.ext hEq)
  exact hpre.subset (by
    intro z hz
    have hnonzero :
        (z : ℂ) ≠ 0 ∧ ‖(z : ℂ)‖ < ρ :=
      entireFunctionJensenRadialGapSummand_support_subset_nonzeroClosedDisk F hF z hz
    exact ⟨le_of_lt hnonzero.2, z.2⟩)

/-- Classical Jensen finite-zero divisor input in a closed disk, with
multiplicities.

This is the divisor-finiteness part of the nonzero-origin Jensen package: a
nontrivial entire function has only finitely many zeros in each compact disk,
and the closed-disk multiplicity family is therefore summable after the origin
summand is removed. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisor_closedDiskMultiplicitySummable_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    [Decidable (F 0 = 0)]
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [DecidableEq (EntireFunctionZero F)] :
    ∀ R : ℝ,
      1 ≤ R →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) := by
  intro R _hR
  letI : ∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R) :=
    fun z => inferInstance
  exact summable_of_finite_support
    (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
      F hF hF0 R)

/-- Classical Jensen radial-gap divisor summability for a nonzero value at the
origin.

The radial-gap summand is supported on the finite zero divisor in the open
disk of radius `ρ`, counted by analytic multiplicity. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummability_from_finiteZeroDivisor_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)] :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) := by
  intro ρ _hρ
  letI : ∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ) :=
    fun z => inferInstance
  exact summable_of_finite_support
    (entireFunctionJensenRadialGapSummand_support_finite F hF hF0 ρ)

/-- A single nonzero zero strictly inside the Jensen circle contributes exactly
its multiplicity times the radial logarithmic factor.

This is the pointwise zero-factor calculation in the product proof of Jensen's
formula. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFactor_radialContribution_identity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (z : EntireFunctionZero F)
    (hz0 : (z : ℂ) ≠ 0)
    (hzρ : ‖(z : ℂ)‖ < ρ) :
    entireFunctionJensenRadialGapSummand F hF ρ z =
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        Real.log (ρ / ‖(z : ℂ)‖) := by
  exact entireFunctionJensenRadialGapSummand_eq_mul_log_of_lt
    F hF z hz0 hzρ

/-- A zero outside the open Jensen disk contributes no radial-gap term. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFactor_radialContribution_eq_zero_of_not_lt
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (z : EntireFunctionZero F)
    (hzρ : ¬ ‖(z : ℂ)‖ < ρ) :
    entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
  match (inferInstance : Decidable ((z : ℂ) = 0)) with
  | isTrue hz0 =>
      exact entireFunctionJensenRadialGapSummand_eq_zero_of_zero F hF z hz0
  | isFalse hz0 =>
      exact entireFunctionJensenRadialGapSummand_eq_zero_of_not_lt F hF z hz0 hzρ

/-- The origin zero is absent from the nonzero-origin Jensen radial-gap sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_origin_radialContribution_eq_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (z : EntireFunctionZero F)
    (hz0 : (z : ℂ) = 0) :
    entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
  exact entireFunctionJensenRadialGapSummand_eq_zero_of_zero F hF z hz0

/-- The finite product radial-gap sum attached to the zero divisor inside the
Jensen circle.

The indexing finset is supplied by divisor finiteness; this definition keeps
the finite product stage separate from the later infinite-sum transport. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (s : Finset (EntireFunctionZero F)) : ℝ :=
  ∑ z in s, entireFunctionJensenRadialGapSummand F hF ρ z

/-- The finite product radial-gap sum is literally the sum of the pointwise
zero-factor radial contributions over the chosen finite zero divisor. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProduct_sum_identity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (s : Finset (EntireFunctionZero F)) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ s =
      ∑ z in s, entireFunctionJensenRadialGapSummand F hF ρ z := by
  rfl

/-- Finite-product zero-factor expansion: once the finite zero divisor has been
chosen, its Jensen contribution is the sum of the explicit nonzero radial
factors, with origin and exterior terms contributing zero by the pointwise
lemmas above. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProduct_explicit_sum_identity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (s : Finset (EntireFunctionZero F)) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ s =
      ∑ z in s,
        if (z : ℂ) = 0 then
          0
        else if ‖(z : ℂ)‖ < ρ then
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log (ρ / ‖(z : ℂ)‖)
        else
          0 := by
  change
    (∑ z in s, entireFunctionJensenRadialGapSummand F hF ρ z) =
      ∑ z in s,
        if (z : ℂ) = 0 then
          0
        else if ‖(z : ℂ)‖ < ρ then
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log (ρ / ‖(z : ℂ)‖)
        else
          0
  exact
    Finset.sum_congr rfl
      (fun z _hz => by
        change
          (if hz0 : (z : ℂ) = 0 then
            0
          else if ‖(z : ℂ)‖ < ρ then
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log (ρ / ‖(z : ℂ)‖)
          else
            0) =
          (if (z : ℂ) = 0 then
            0
          else if ‖(z : ℂ)‖ < ρ then
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log (ρ / ‖(z : ℂ)‖)
          else
            0)
        match (inferInstance : Decidable ((z : ℂ) = 0)) with
        | isTrue hz0 => exact Eq.trans (dif_pos hz0) (if_pos hz0).symm
        | isFalse hz0 => exact Eq.trans (dif_neg hz0) (if_neg hz0).symm)

/-- If a finite zero divisor contains the support of the Jensen radial-gap
summand, the infinite radial-gap sum is the corresponding finite product
radial-gap sum.

This is the constructive support-controlled bridge from divisor finiteness to
the product formula: the product stage may use any explicit finite support
certificate, without choosing a canonical enumeration of zeros. -/
theorem entireFunctionJensenRadialGapSum_eq_finiteProductRadialGapSum_of_support_subset
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (s : Finset (EntireFunctionZero F))
    (hsupport :
      Function.support
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) ⊆
        (s : Set (EntireFunctionZero F))) :
    entireFunctionJensenRadialGapSum F hF ρ =
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ s := by
  change
    (∑' z : EntireFunctionZero F,
      entireFunctionJensenRadialGapSummand F hF ρ z) =
      ∑ z in s, entireFunctionJensenRadialGapSummand F hF ρ z
  exact tsum_eq_sum
    (s := s)
    (fun z hz_not_mem => by
      match (inferInstance :
          Decidable (entireFunctionJensenRadialGapSummand F hF ρ z = 0)) with
      | isTrue hz_zero => exact hz_zero
      | isFalse hz_ne_zero =>
          have hz_support :
              z ∈ Function.support
                (fun w : EntireFunctionZero F =>
                  entireFunctionJensenRadialGapSummand F hF ρ w) :=
            hz_ne_zero
          exact False.elim (hz_not_mem (hsupport hz_support)))

/-- If the Jensen disk contains no nonzero zeros, the radial-gap divisor sum is
zero.

This is the zero-free quotient special case of the finite-divisor product
bridge: once all possible nonzero zero factors are absent from the disk, the
entire radial-gap contribution vanishes term by term. -/
theorem entireFunctionJensenRadialGapSum_eq_zero_of_no_nonzero_zeros_in_disk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (hzero :
      ∀ z : EntireFunctionZero F,
        (z : ℂ) ≠ 0 →
        ¬ ‖(z : ℂ)‖ < ρ) :
    entireFunctionJensenRadialGapSum F hF ρ = 0 := by
  change
    (∑' z : EntireFunctionZero F,
      entireFunctionJensenRadialGapSummand F hF ρ z) = 0
  have hterm : ∀ z : EntireFunctionZero F, entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
    intro z
    change
      (if hz0 : (z : ℂ) = 0 then
        0
      else if ‖(z : ℂ)‖ < ρ then
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log (ρ / ‖(z : ℂ)‖)
      else
        0) = 0
    match (inferInstance : Decidable ((z : ℂ) = 0)) with
    | isTrue hz0 => exact dif_pos hz0
    | isFalse hz0 => exact Eq.trans (dif_neg hz0) (if_neg (hzero z hz0))
  calc
    (∑' z : EntireFunctionZero F,
      entireFunctionJensenRadialGapSummand F hF ρ z)
        = ∑' _z : EntireFunctionZero F, 0 := by
          exact tsum_congr hterm
    _ = 0 := tsum_zero

/-- The finite closed-disk divisor supporting the nonzero multiplicity summand.

This is the closed-disk divisor side of Jensen's formula after the origin
factor has been removed: it is exactly the finite support of the nonzero
closed-disk multiplicity family. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (R : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)] :
    Finset (EntireFunctionZero F) :=
  (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
    F hF hF0 R).toFinset

/-- The closed-disk finite divisor contains the support of the nonzero
multiplicity summand. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_contains_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (R : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)] :
    Function.support
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) ⊆
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 R : Set (EntireFunctionZero F)) := by
  intro z hz
  change
    z ∈
      ((entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
        F hF hF0 R).toFinset : Set (EntireFunctionZero F))
  exact
    (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
      F hF hF0 R).mem_toFinset.2 hz

/-- The nonzero closed-disk multiplicity family has the finite sum over its
closed-disk divisor as its infinite sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSummand_hasSum_supportFiniteZeroDivisor
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (R : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ R)] :
    HasSum
      (fun z : EntireFunctionZero F =>
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 R,
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) := by
  exact hasSum_sum_of_ne_finset_zero
    (s :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 R)
    (f := fun z : EntireFunctionZero F =>
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)
    (fun z hz_not_mem => by
      match (inferInstance :
          Decidable (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z = 0)) with
      | isTrue hz_zero => exact hz_zero
      | isFalse hz_ne =>
          have hz_support :
              z ∈ Function.support
                (fun w : EntireFunctionZero F =>
                  entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R w) :=
            hz_ne
          have hz_mem :
              z ∈
                entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
                  F hF hF0 R :=
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_contains_support
              F hF hF0 R hz_support
          exact False.elim (hz_not_mem hz_mem))

/-- The finite zero divisor supporting the Jensen radial-gap summand.

This is the finite divisor used in the product side of Jensen's formula: it is
the support of the nonzero zero factors strictly inside the Jensen circle. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)] :
    Finset (EntireFunctionZero F) :=
  (entireFunctionJensenRadialGapSummand_support_finite F hF hF0 ρ).toFinset

/-- The radial-gap finite divisor contains the support of the Jensen radial-gap
summand. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_contains_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)] :
    Function.support
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) ⊆
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ : Set (EntireFunctionZero F)) := by
  intro z hz
  change
    z ∈
      ((entireFunctionJensenRadialGapSummand_support_finite
        F hF hF0 ρ).toFinset : Set (EntireFunctionZero F))
  exact
    (entireFunctionJensenRadialGapSummand_support_finite F hF hF0 ρ).mem_toFinset.2 hz

/-- The strictly interior part of the closed-disk zero divisor.  This is the
closed-support side that should compare with the radial-gap divisor. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ ρ)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)] :
    Finset (EntireFunctionZero F) :=
  (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
    F hF hF0 ρ).filter
    (fun z : EntireFunctionZero F => ‖(z : ℂ)‖ < ρ)

/-- The boundary part of the closed-disk zero divisor.  These zeros are
extracted by the closed-support quotient but contribute no radial-gap summand. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ ρ)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)] :
    Finset (EntireFunctionZero F) :=
  (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
    F hF hF0 ρ).filter
    (fun z : EntireFunctionZero F => ¬ ‖(z : ℂ)‖ < ρ)

/-- Boundary members of the closed-disk divisor have zero radial-gap summand. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor_radialGapSummand_eq_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ ρ)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
          F hF hF0 ρ) :
    entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
  have hz_not_lt : ¬ ‖(z : ℂ)‖ < ρ :=
    (Finset.mem_filter.1 hz).2
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFactor_radialContribution_eq_zero_of_not_lt
      F hF ρ z hz_not_lt

/-- Every closed-disk support divisor member is nonzero. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ ρ)]
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    (z : ℂ) ≠ 0 := by
  have hsupport :
      z ∈ Function.support
        (fun w : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF ρ w) := by
    change
      z ∈
        (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
          F hF hF0 ρ).toFinset at hz
    exact
      (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
        F hF hF0 ρ).mem_toFinset.1 hz
  intro hz0
  exact hsupport
    (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_zero_of_eq_zero
      F hF z hz0)

/-- Every closed-disk support divisor member lies in the closed disk. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_norm_le
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ ρ)]
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    ‖(z : ℂ)‖ ≤ ρ := by
  have hsupport :
      z ∈ Function.support
        (fun w : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF ρ w) := by
    change
      z ∈
        (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
          F hF hF0 ρ).toFinset at hz
    exact
      (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
        F hF hF0 ρ).mem_toFinset.1 hz
  have hz_nonzero :
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF ρ z ≠ 0 := by
    intro hz0
    exact hsupport hz0
  have hz0 : (z : ℂ) ≠ 0 := by
    intro hz0
    exact hz_nonzero
      (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_zero_of_eq_zero
        F hF z hz0)
  match (inferInstance : Decidable (‖(z : ℂ)‖ ≤ ρ)) with
  | isTrue hle => exact hle
  | isFalse hle =>
      exact False.elim
        (hz_nonzero
          (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_eq_zero_of_not_closedDisk
            F hF z hz0 hle))

/-- Boundary support members lie exactly on the Jensen boundary circle. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor_mem_norm_eq
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable ((z : ℂ) = 0)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ ≤ ρ)]
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)]
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
          F hF hF0 ρ) :
    ‖(z : ℂ)‖ = ρ := by
  have hz_closed :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ :=
    (Finset.mem_filter.1 hz).1
  have hle : ‖(z : ℂ)‖ ≤ ρ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_norm_le
      F hF hF0 ρ z hz_closed
  have hnot_lt : ¬ ‖(z : ℂ)‖ < ρ :=
    (Finset.mem_filter.1 hz).2
  exact le_antisymm hle (le_of_not_gt hnot_lt)

end
end LFunctions
end Boundary
