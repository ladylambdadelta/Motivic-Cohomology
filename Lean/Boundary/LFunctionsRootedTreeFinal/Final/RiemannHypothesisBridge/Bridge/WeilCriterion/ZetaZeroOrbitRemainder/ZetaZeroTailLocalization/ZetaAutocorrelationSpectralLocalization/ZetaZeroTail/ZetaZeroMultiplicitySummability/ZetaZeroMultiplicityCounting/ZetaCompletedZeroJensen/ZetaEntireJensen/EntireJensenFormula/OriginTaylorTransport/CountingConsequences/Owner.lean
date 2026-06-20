import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.OriginTaylorTransport.JensenOriginTransport.Owner

/-!
# Origin Taylor transport and zero-counting consequences

This owner layer was split from `OriginTaylorTransport.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Classical Jensen formula in radial-gap form, with multiplicities and with
the first nonzero Taylor factor at the origin absorbed into an additive
constant.

This is the precise large-radius analytic input after removing the origin
factor: Jensen's formula identifies the multiplicity-weighted radial gap sum
with the boundary logarithmic average up to a fixed additive normalization
constant. The restriction `1 ≤ ρ` is the exact place where the origin-radius
term is nonnegative and can be absorbed. -/
theorem entireFunction_classicalJensenFormula_radialGapSum_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ ≤
            J + entireFunctionJensenBoundaryLogAverage F ρ) ∧
      (∀ R : ℝ,
          1 ≤ R →
          entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
            J + entireFunctionJensenRadialGapSum F hF (2 * R)) := by
  exact
    Exists.elim
      (entireFunction_classicalJensenFormula_originFactoredRadialGapSum_le_boundaryLogAverage
        F hF hnontrivial)
      (fun J hJ =>
        have hclosed :
            ∀ R : ℝ,
              1 ≤ R →
              Summable
                (fun z : EntireFunctionZero F =>
                  entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) :=
          fun R hR =>
            entireFunctionZeroMultiplicityClosedDiskSummable_of_nonzeroClosedDiskSummable
              F hF (hJ.1 R hR)
        have hradial :
            ∀ ρ : ℝ,
              1 ≤ ρ →
              Summable
                  (fun z : EntireFunctionZero F =>
                    entireFunctionJensenRadialGapSummand F hF ρ z) ∧
                entireFunctionJensenRadialGapSum F hF ρ ≤
                  entireFunctionOriginMultiplicityLogContribution F hF + |J| +
                    entireFunctionJensenBoundaryLogAverage F ρ :=
          fun ρ hρ =>
            match hJ.2 ρ hρ with
            | ⟨hgap, hbound⟩ =>
                have hJ_le :
                    J + entireFunctionJensenBoundaryLogAverage F ρ ≤
                      entireFunctionOriginMultiplicityLogContribution F hF + |J| +
                        entireFunctionJensenBoundaryLogAverage F ρ := by
                  have hJ_abs : J ≤ |J| := le_abs_self J
                  have horigin_nonneg :
                      0 ≤ entireFunctionOriginMultiplicityLogContribution F hF := by
                    calc
                      0 ≤ (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2 :=
                        mul_nonneg
                          (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF 0))
                          real_log_two_pos.le
                      _ = entireFunctionOriginMultiplicityLogContribution F hF := rfl
                  have hJ_shift :
                      J + entireFunctionJensenBoundaryLogAverage F ρ ≤
                        |J| + entireFunctionJensenBoundaryLogAverage F ρ :=
                    add_le_add_right hJ_abs
                      (entireFunctionJensenBoundaryLogAverage F ρ)
                  have horigin_shift :
                      |J| + entireFunctionJensenBoundaryLogAverage F ρ ≤
                        entireFunctionOriginMultiplicityLogContribution F hF +
                          (|J| + entireFunctionJensenBoundaryLogAverage F ρ) :=
                    le_add_of_nonneg_left horigin_nonneg
                  have hassoc :
                      entireFunctionOriginMultiplicityLogContribution F hF +
                          (|J| + entireFunctionJensenBoundaryLogAverage F ρ) =
                        entireFunctionOriginMultiplicityLogContribution F hF + |J| +
                          entireFunctionJensenBoundaryLogAverage F ρ :=
                    (add_assoc
                      (entireFunctionOriginMultiplicityLogContribution F hF)
                      |J|
                      (entireFunctionJensenBoundaryLogAverage F ρ)).symm
                  have horigin_target :
                      |J| + entireFunctionJensenBoundaryLogAverage F ρ ≤
                        entireFunctionOriginMultiplicityLogContribution F hF + |J| +
                          entireFunctionJensenBoundaryLogAverage F ρ :=
                    Eq.subst
                      (motive := fun x : ℝ =>
                        |J| + entireFunctionJensenBoundaryLogAverage F ρ ≤ x)
                      hassoc
                      horigin_shift
                  exact le_trans hJ_shift horigin_target
                And.intro hgap (le_trans hbound hJ_le)
        have hcounting :
            ∀ R : ℝ,
              1 ≤ R →
              entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
                entireFunctionOriginMultiplicityLogContribution F hF + |J| +
                  entireFunctionJensenRadialGapSum F hF (2 * R) :=
          fun R hR =>
            have hρ : 1 ≤ 2 * R :=
              one_le_doubled_radius_of_one_le hR
            have hradial_at :
                Summable
                    (fun z : EntireFunctionZero F =>
                      entireFunctionJensenRadialGapSummand F hF (2 * R) z) ∧
                  entireFunctionJensenRadialGapSum F hF (2 * R) ≤
                    J + entireFunctionJensenBoundaryLogAverage F (2 * R) :=
              hJ.2 (2 * R) hρ
            have hgap :
                Summable
                  (fun z : EntireFunctionZero F =>
                    entireFunctionJensenRadialGapSummand F hF (2 * R) z) :=
              hradial_at.1
            have hcount :
                entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
                  entireFunctionOriginMultiplicityLogContribution F hF +
                    entireFunctionJensenRadialGapSum F hF (2 * R) :=
              entireFunctionZeroMultiplicityCountingInClosedDisk_mul_log_two_le_originContribution_plus_radialGapSum
                F hF hR (hJ.1 R hR) hgap
            have habs_nonneg : 0 ≤ |J| := abs_nonneg J
            have hshift :
                entireFunctionOriginMultiplicityLogContribution F hF +
                    entireFunctionJensenRadialGapSum F hF (2 * R) ≤
                  entireFunctionOriginMultiplicityLogContribution F hF +
                    (|J| + entireFunctionJensenRadialGapSum F hF (2 * R)) :=
              add_le_add_left
                (le_add_of_nonneg_left habs_nonneg)
                (entireFunctionOriginMultiplicityLogContribution F hF)
            have hassoc :
                entireFunctionOriginMultiplicityLogContribution F hF +
                    (|J| + entireFunctionJensenRadialGapSum F hF (2 * R)) =
                  entireFunctionOriginMultiplicityLogContribution F hF + |J| +
                    entireFunctionJensenRadialGapSum F hF (2 * R) :=
              (add_assoc
                (entireFunctionOriginMultiplicityLogContribution F hF)
                |J|
                (entireFunctionJensenRadialGapSum F hF (2 * R))).symm
            le_trans hcount
              (Eq.subst
                (motive := fun x : ℝ =>
                  entireFunctionOriginMultiplicityLogContribution F hF +
                    entireFunctionJensenRadialGapSum F hF (2 * R) ≤ x)
                hassoc
                hshift)
        Exists.intro
          (entireFunctionOriginMultiplicityLogContribution F hF + |J|)
          (And.intro hclosed (And.intro hradial hcounting)))

/-- Jensen's radial-gap formula supplies summability of closed-disk
multiplicity summands. -/
theorem entireFunction_classicalJensenFormula_closedDiskMultiplicitySummable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∀ R : ℝ,
      1 ≤ R →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) := by
  intro R hR
  exact
    Exists.elim
      (entireFunction_classicalJensenFormula_radialGapSum_le_boundaryLogAverage
        F hF hnontrivial)
      (fun _J hJ =>
        hJ.1 R hR)

/-- The doubled-radius algebra converting the weighted Jensen radial-gap bound
into the closed-disk zero-counting estimate. -/
theorem entireFunction_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hweighted :
      ∃ J : ℝ,
        ∀ R : ℝ,
          1 ≤ R →
          entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
            J + entireFunctionJensenBoundaryLogAverage F (2 * R)) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    Exists.elim hweighted
      (fun J hJ =>
        Exists.intro ((Real.log 2)⁻¹ * J)
          (fun R hR =>
            have hlog_pos : 0 < Real.log 2 :=
              real_log_two_pos
            have hscaled :
                (Real.log 2)⁻¹ *
                    (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2) ≤
                  (Real.log 2)⁻¹ *
                    (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) := by
              exact mul_le_mul_of_nonneg_left (hJ R hR) real_log_two_inv_nonneg
            have hleft :
                (Real.log 2)⁻¹ *
                    (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2) =
                  entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
              calc
                (Real.log 2)⁻¹ *
                    (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2) =
                    (Real.log 2)⁻¹ *
                      (Real.log 2 * entireFunctionZeroMultiplicityCountingInClosedDisk F hF R) := by
                  exact congrArg
                    (fun x : ℝ => (Real.log 2)⁻¹ * x)
                    (mul_comm
                      (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R)
                      (Real.log 2))
                _ =
                    ((Real.log 2)⁻¹ * Real.log 2) *
                      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
                  exact
                    (mul_assoc
                      (Real.log 2)⁻¹
                      (Real.log 2)
                      (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R)).symm
                _ = 1 * entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
                  exact congrArg
                    (fun x : ℝ => x *
                      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R)
                    (inv_mul_cancel₀ hlog_pos.ne')
                _ = entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
                  exact one_mul _
            have hright :
                (Real.log 2)⁻¹ *
                    (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) =
                  (Real.log 2)⁻¹ * J +
                    (Real.log 2)⁻¹ * entireFunctionJensenBoundaryLogAverage F (2 * R) := by
              exact mul_add
                (Real.log 2)⁻¹
                J
                (entireFunctionJensenBoundaryLogAverage F (2 * R))
            hleft ▸ hright ▸ hscaled))

/-- Classical Jensen formula in the weighted doubled-radius counting form.

This is the genuine classical Jensen formula input after factoring the first
nonzero Taylor term at the origin: the Jensen radial-gap sum on the circle of
radius `2R` dominates the multiplicity count in `closedDisk R` by the uniform
gap `log 2`, with a constant absorbing the origin factor; cf. Titchmarsh, *The
Theory of Functions*, §5. -/
theorem entireFunction_classicalJensenFormula_weighted_doubledRadius_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
          J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    Exists.elim
      (entireFunction_classicalJensenFormula_radialGapSum_le_boundaryLogAverage
        F hF hnontrivial)
      (fun J hJ =>
        Exists.intro (J + J)
          (fun R hR =>
            have hρ : 1 ≤ 2 * R :=
              one_le_doubled_radius_of_one_le hR
            have hradial_at :
                Summable
                    (fun z : EntireFunctionZero F =>
                      entireFunctionJensenRadialGapSummand F hF (2 * R) z) ∧
                  entireFunctionJensenRadialGapSum F hF (2 * R) ≤
                    J + entireFunctionJensenBoundaryLogAverage F (2 * R) :=
              hJ.2.1 (2 * R) hρ
            have hgap_bound :
                entireFunctionJensenRadialGapSum F hF (2 * R) ≤
                  J + entireFunctionJensenBoundaryLogAverage F (2 * R) :=
              hradial_at.2
            have hcount_gap :
                entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
                  J + entireFunctionJensenRadialGapSum F hF (2 * R) :=
              hJ.2.2 R hR
            have hbound :
                J + entireFunctionJensenRadialGapSum F hF (2 * R) ≤
                  J + (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) :=
              add_le_add_left hgap_bound J
            have htarget :
                J + (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) =
                  J + J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
              exact
                (add_assoc J J
                  (entireFunctionJensenBoundaryLogAverage F (2 * R))).symm
            Eq.subst
              (motive := fun x : ℝ =>
                entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤ x)
              htarget
              (le_trans hcount_gap hbound)))

/-- Classical weighted Jensen zero-counting estimate on the doubled disk. -/
theorem entireFunction_classicalJensenFormula_weighted_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
          J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_classicalJensenFormula_weighted_doubledRadius_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
      F hF hnontrivial

/-- Standard Jensen formula with multiplicity counting on the doubled disk.

After factoring the first nonzero Taylor term at the origin, Jensen's formula
gives the weighted sum of logarithmic radial gaps for zeros in the doubled
disk.  Since every zero in `closedDisk R` contributes at least `log 2` to that
sum when the boundary radius is `2R`, the stated inequality follows with a
constant absorbing the origin factor. -/
theorem entireFunction_classicalJensenFormula_standardRoot_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  have hweighted :
      ∃ J : ℝ,
        ∀ R : ℝ,
          1 ≤ R →
          entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
            J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
    exact
      entireFunction_classicalJensenFormula_weighted_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
        F hF hnontrivial
  exact
    entireFunction_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hweighted

/-- Classical Jensen formula zero-counting estimate, including the doubled-radius
`log 2` loss.

This is the deepest remaining analytic input: Jensen's formula for a nonzero
entire function, with multiplicities, after comparing zeros in `closedDisk R`
to the boundary integral on the circle of radius `2R`; cf. Titchmarsh, *The
Theory of Functions*, §5. -/
theorem entireFunction_classicalJensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_classicalJensenFormula_standardRoot_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hnontrivial

/-- Standard Jensen zero-counting estimate for nontrivial entire functions,
including the algebraic doubled-radius `log 2` loss. -/
theorem entireFunction_standardJensen_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_classicalJensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hnontrivial

/-- Classical Jensen zero-counting estimate for nontrivial entire functions,
with the doubled-radius `log 2` loss. -/
theorem entireFunction_jensen_formula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_standardJensen_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hnontrivial


/-- Jensen's formula relates multiplicity-aware closed-disk zero counting to the
normalized logarithmic boundary average on the doubled circle, with the standard
`log 2` loss.

This is the classical analytic root: after factoring the first nonzero Taylor
term at the origin, Jensen's formula bounds zeros in `closedDisk R` by the
boundary average of `log ‖F‖` on the circle of radius `2R`, divided by
`log 2`; cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_jensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact entireFunction_jensen_formula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    F hF hnontrivial

/-- Multiplicity-aware closed-disk zero counting is bounded by the doubled-circle
boundary logarithmic average with the standard `log 2` factor. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = 2 * R ∧ x = Real.log ‖F z‖} ∧
        IntervalIntegrable
          (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
          MeasureTheory.volume
          (0 : ℝ)
          (2 * Real.pi) ∧
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    match
      entireFunction_jensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
        F hF hnontrivial with
    | ⟨J, hcount⟩ =>
        Exists.intro J
          (fun R hR =>
            match entireFunction_jensenBoundaryLogAverage_regularity F hF hnontrivial R hR with
            | ⟨hbdd, hint⟩ =>
                ⟨hbdd, hint, hcount R hR⟩)

/-- Jensen's formula converts the boundary-log-average estimate into the log-max
closed-disk zero-counting bound. -/
theorem entireFunction_jensenFormula_zeroMultiplicityCounting_closedDisk_le_logMax
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ * entireFunctionLogMaxOnCircle F (2 * R) := by
  exact
    match
      entireFunctionZeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
        F hF hnontrivial with
    | ⟨J, hJ⟩ =>
        Exists.intro J
          (fun R hR =>
            have hR_nonneg : 0 ≤ R :=
              le_trans zero_le_one hR
            have htwoR_nonneg : 0 ≤ 2 * R :=
              mul_nonneg zero_le_two hR_nonneg
            match hJ R hR with
            | ⟨hbdd, hint, hcount⟩ =>
                have havg :
                    entireFunctionJensenBoundaryLogAverage F (2 * R) ≤
                      entireFunctionLogMaxOnCircle F (2 * R) :=
                  entireFunctionJensenBoundaryLogAverage_le_logMaxOnCircle
                    F
                    htwoR_nonneg
                    hbdd
                    hint
                have hlog_two_nonneg : 0 ≤ (Real.log 2)⁻¹ :=
                  inv_nonneg.mpr (le_of_lt (Real.log_pos one_lt_two))
                have hwith_constant :
                    J + (Real.log 2)⁻¹ *
                        entireFunctionJensenBoundaryLogAverage F (2 * R) ≤
                      J + (Real.log 2)⁻¹ *
                        entireFunctionLogMaxOnCircle F (2 * R) :=
                  add_le_add_left
                    (mul_le_mul_of_nonneg_left havg hlog_two_nonneg)
                    J
                le_trans hcount hwith_constant)


end
end LFunctions
end Boundary
