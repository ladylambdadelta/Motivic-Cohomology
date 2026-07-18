import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part23

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The raw deleted-circle boundary at `0` has the expected `2πi` pole-residue value. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_zeroPole_eq_twoPiI_smul_residue
    (f : ZetaAdmissibleFunction)
    {R : ℝ} (hR : 0 < R)
    (s : Set ℂ) (hs : s.Countable)
      (hcontinuous :
        ContinuousOn
          (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) R \ {(0 : ℂ)}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) R \ {(0 : ℂ)}) \ s →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z)
      (hlocal :
        Tendsto
          (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (𝓝[≠] (0 : ℂ))
        (𝓝 (explicitFormulaRectangle_zeroPoleResidue f))) :
    explicitFormulaRectangleRawDeletedCircleBoundary f R 0 =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_zeroPoleResidue f := by
  exact
    explicitFormulaRectangle_zeroPole_deletedCircleIntegral_eq_twoPiI_smul_residue
      f hR s hs hcontinuous hdifferentiable hlocal

/-- The raw deleted-circle boundary at `1` has the expected `2πi` pole-residue value. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_onePole_eq_twoPiI_smul_residue
    (f : ZetaAdmissibleFunction)
    {R : ℝ} (hR : 0 < R)
    (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) R \ {(1 : ℂ)}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) R \ {(1 : ℂ)}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hlocal :
      Tendsto
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (𝓝[≠] (1 : ℂ))
        (𝓝 (explicitFormulaRectangle_onePoleResidue f))) :
    explicitFormulaRectangleRawDeletedCircleBoundary f R 1 =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_onePoleResidue f := by
  exact
    explicitFormulaRectangle_onePole_deletedCircleIntegral_eq_twoPiI_smul_residue
      f hR s hs hcontinuous hdifferentiable hlocal

/-- The raw deleted-circle boundary at `0` has the expected `2πi` pole-residue value
once the local regularity on the deleted disk is supplied.  The pole coefficient itself is
the owner-proved completed-zeta coefficient `+1`. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_zeroPole_eq_twoPiI_smul_residue_of_regular
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R)
    (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn
        (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (0 : ℂ) R \ {(0 : ℂ)}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) R \ {(0 : ℂ)}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z) :
    explicitFormulaRectangleRawDeletedCircleBoundary f R 0 =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_zeroPoleResidue f := by
  have hlocal_raw :
      Tendsto
        (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (explicitFormulaRectangle_zeroPoleResidue f)) :=
    explicitFormulaRectangle_zeroPole_localResidue_tendsto_rawCompleted f hPhi
  have hcoeff :
      (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z) =
        (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z) := by
    funext z
    exact congrArg
      (fun x : ℂ => x * zetaCompletedExplicitFormulaContourIntegrand f z)
      (sub_zero z).symm
  have hlocal_shifted :
      Tendsto
        (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (explicitFormulaRectangle_zeroPoleResidue f)) :=
    Eq.subst
      (motive := fun φ : ℂ → ℂ =>
        Tendsto φ (𝓝[≠] (0 : ℂ)) (𝓝 (explicitFormulaRectangle_zeroPoleResidue f)))
      hcoeff
      hlocal_raw
  exact
    explicitFormulaRectangleRawDeletedCircleBoundary_zeroPole_eq_twoPiI_smul_residue
      f hR s hs hcontinuous hdifferentiable
      hlocal_shifted

/-- The raw deleted-circle boundary at `1` has the expected `2πi` pole-residue value
once the local regularity on the deleted disk is supplied.  The pole coefficient itself is
the owner-proved completed-zeta coefficient `+1`. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_onePole_eq_twoPiI_smul_residue_of_regular
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {R : ℝ} (hR : 0 < R)
    (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) R \ {(1 : ℂ)}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) R \ {(1 : ℂ)}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z) :
    explicitFormulaRectangleRawDeletedCircleBoundary f R 1 =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_onePoleResidue f := by
  exact
    explicitFormulaRectangleRawDeletedCircleBoundary_onePole_eq_twoPiI_smul_residue
      f hR s hs hcontinuous hdifferentiable
      (explicitFormulaRectangle_onePole_localResidue_tendsto_rawCompleted f hPhi)

/-- The raw deleted-circle boundary at a completed-zero coordinate has the expected
`2πi` completed-zero residue value. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_completedZero_eq_twoPiI_smul_residue
    (f : ZetaAdmissibleFunction) (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T)
    {R : ℝ} (hR : 0 < R)
    (s : Set ℂ) (hs : s.Countable)
    (hcontinuous :
      ContinuousOn
        (fun z : ℂ =>
          (z - completedZeroResidueCoordinate ρ) *
            zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (completedZeroResidueCoordinate ρ) R \
          {completedZeroResidueCoordinate ρ}))
    (hdifferentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) R \
            {completedZeroResidueCoordinate ρ}) \ s →
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (w - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hlocal :
      ∀ σ : {σ : ℂ // ZetaCompletedZero σ},
        σ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate σ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate σ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero σ)))) :
    explicitFormulaRectangleRawDeletedCircleBoundary f R
        (completedZeroResidueCoordinate ρ) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) := by
  exact
    explicitFormulaRectangle_completedZero_deletedCircleIntegral_eq_twoPiI_smul_residue
      f T ρ hρ hR s hs hcontinuous hdifferentiable hlocal

/-- Case-split deleted-circle evaluation on the raw singular-coordinate carrier.

This is the canonical circle-side bridge for common-value constructions: every raw
coordinate is either `0`, `1`, or a completed-zero residue coordinate, and the existing
one-coordinate deleted-circle residue theorem supplies the corresponding value. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_eq_twoPiI_smul_residue_cases_of_mem
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (T : ℝ) {R : ℝ} (hR : 0 < R)
    (s0 s1 : Set ℂ) (hs0 : s0.Countable) (hs1 : s1.Countable)
    (szero : {ρ : ℂ // ZetaCompletedZero ρ} → Set ℂ)
    (hszero :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          (szero ρ).Countable)
      (hzero_continuous :
        ContinuousOn
          (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) R \ {(0 : ℂ)}))
    (hzero_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) R \ {(0 : ℂ)}) \ s0 →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z)
    (hone_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) R \ {(1 : ℂ)}))
    (hone_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) R \ {(1 : ℂ)}) \ s1 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hcompleted_continuous :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          ContinuousOn
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall (completedZeroResidueCoordinate ρ) R \
              {completedZeroResidueCoordinate ρ}))
    (hcompleted_differentiable :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
          ∀ z : ℂ,
            z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) R \
                {completedZeroResidueCoordinate ρ}) \ szero ρ →
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  (w - completedZeroResidueCoordinate ρ) *
                    zetaCompletedExplicitFormulaContourIntegrand f w)
                z)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))))
    {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (a = 0 ∧
        explicitFormulaRectangleRawDeletedCircleBoundary f R a =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_zeroPoleResidue f) ∨
      (a = 1 ∧
        explicitFormulaRectangleRawDeletedCircleBoundary f R a =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_onePoleResidue f) ∨
      (∃ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∃ _hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
          completedZeroResidueCoordinate ρ = a ∧
            explicitFormulaRectangleRawDeletedCircleBoundary f R a =
              (2 * ↑Real.pi * Complex.I : ℂ) •
                explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) := by
  match explicitFormulaRectangleRawSingularCoordinates_cases T ha with
  | Or.inl hzero_coord =>
      have hcircle_zero :
          explicitFormulaRectangleRawDeletedCircleBoundary f R 0 =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaRectangle_zeroPoleResidue f :=
        explicitFormulaRectangleRawDeletedCircleBoundary_zeroPole_eq_twoPiI_smul_residue_of_regular
          f hPhi hR s0 hs0 hzero_continuous hzero_differentiable
      have hcircle_a :
          explicitFormulaRectangleRawDeletedCircleBoundary f R a =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaRectangle_zeroPoleResidue f :=
        Eq.subst
          (motive := fun z : ℂ =>
            explicitFormulaRectangleRawDeletedCircleBoundary f R z =
              (2 * ↑Real.pi * Complex.I : ℂ) •
                explicitFormulaRectangle_zeroPoleResidue f)
          hzero_coord.symm
          hcircle_zero
      exact Or.inl (And.intro hzero_coord hcircle_a)
  | Or.inr hnot_zero =>
      match hnot_zero with
      | Or.inl hone_coord =>
          have hcircle_one :
              explicitFormulaRectangleRawDeletedCircleBoundary f R 1 =
                (2 * ↑Real.pi * Complex.I : ℂ) •
                  explicitFormulaRectangle_onePoleResidue f :=
            explicitFormulaRectangleRawDeletedCircleBoundary_onePole_eq_twoPiI_smul_residue_of_regular
              f hPhi hR s1 hs1 hone_continuous hone_differentiable
          have hcircle_a :
              explicitFormulaRectangleRawDeletedCircleBoundary f R a =
                (2 * ↑Real.pi * Complex.I : ℂ) •
                  explicitFormulaRectangle_onePoleResidue f :=
            Eq.subst
              (motive := fun z : ℂ =>
                explicitFormulaRectangleRawDeletedCircleBoundary f R z =
                  (2 * ↑Real.pi * Complex.I : ℂ) •
                    explicitFormulaRectangle_onePoleResidue f)
              hone_coord.symm
              hcircle_one
          exact Or.inr (Or.inl (And.intro hone_coord hcircle_a))
      | Or.inr hcompleted =>
          match hcompleted with
          | ⟨ρ, hρ, hcoord⟩ =>
              have hcircle_completed :
                  explicitFormulaRectangleRawDeletedCircleBoundary f R
                      (completedZeroResidueCoordinate ρ) =
                    (2 * ↑Real.pi * Complex.I : ℂ) •
                      explicitFormulaZeroResidue f
                        (explicitFormulaZeroDataOfCompletedZero ρ) :=
                explicitFormulaRectangleRawDeletedCircleBoundary_completedZero_eq_twoPiI_smul_residue
                  f T ρ hρ hR (szero ρ) (hszero ρ hρ)
                  (hcompleted_continuous ρ hρ)
                  (hcompleted_differentiable ρ hρ)
                  hlocal
              have hcircle_a :
                  explicitFormulaRectangleRawDeletedCircleBoundary f R a =
                    (2 * ↑Real.pi * Complex.I : ℂ) •
                      explicitFormulaZeroResidue f
                        (explicitFormulaZeroDataOfCompletedZero ρ) :=
                Eq.subst
                  (motive := fun z : ℂ =>
                    explicitFormulaRectangleRawDeletedCircleBoundary f R z =
                      (2 * ↑Real.pi * Complex.I : ℂ) •
                        explicitFormulaZeroResidue f
                          (explicitFormulaZeroDataOfCompletedZero ρ))
                  hcoord
                  hcircle_completed
              exact Or.inr
                (Or.inr
                  (Exists.intro ρ
                    (Exists.intro hρ
                      (And.intro hcoord hcircle_a))))

/-- Function-level circle common-value supplier on the raw singular-coordinate carrier.

If a proposed common-value function agrees with the canonical residue values at `0`, `1`,
and every completed-zero coordinate in the finite height window, then the existing
deleted-circle residue theorems supply the `hcircle` hypothesis for every raw singular
coordinate. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_eq_commonValue_on_rawSingularCoordinates
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (T : ℝ) {R : ℝ} (hR : 0 < R)
    (value : ℂ → ℂ)
    (hvalue_zero :
      value 0 =
        (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangle_zeroPoleResidue f)
    (hvalue_one :
      value 1 =
        (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangle_onePoleResidue f)
    (hvalue_completed :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
          value (completedZeroResidueCoordinate ρ) =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))
    (s0 s1 : Set ℂ) (hs0 : s0.Countable) (hs1 : s1.Countable)
    (szero : {ρ : ℂ // ZetaCompletedZero ρ} → Set ℂ)
    (hszero :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          (szero ρ).Countable)
      (hzero_continuous :
        ContinuousOn
          (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) R \ {(0 : ℂ)}))
    (hzero_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) R \ {(0 : ℂ)}) \ s0 →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z)
    (hone_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) R \ {(1 : ℂ)}))
    (hone_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) R \ {(1 : ℂ)}) \ s1 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hcompleted_continuous :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          ContinuousOn
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall (completedZeroResidueCoordinate ρ) R \
              {completedZeroResidueCoordinate ρ}))
    (hcompleted_differentiable :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
          ∀ z : ℂ,
            z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) R \
                {completedZeroResidueCoordinate ρ}) \ szero ρ →
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  (w - completedZeroResidueCoordinate ρ) *
                    zetaCompletedExplicitFormulaContourIntegrand f w)
                z)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        explicitFormulaRectangleRawDeletedCircleBoundary f R a = value a := by
  intro a ha
  have hcases :
      (a = 0 ∧
          explicitFormulaRectangleRawDeletedCircleBoundary f R a =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaRectangle_zeroPoleResidue f) ∨
        (a = 1 ∧
          explicitFormulaRectangleRawDeletedCircleBoundary f R a =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaRectangle_onePoleResidue f) ∨
        (∃ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∃ hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
            completedZeroResidueCoordinate ρ = a ∧
              explicitFormulaRectangleRawDeletedCircleBoundary f R a =
                (2 * ↑Real.pi * Complex.I : ℂ) •
                  explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) :=
    explicitFormulaRectangleRawDeletedCircleBoundary_eq_twoPiI_smul_residue_cases_of_mem
      f hPhi T hR s0 s1 hs0 hs1 szero hszero
      hzero_continuous hzero_differentiable
      hone_continuous hone_differentiable
      hcompleted_continuous hcompleted_differentiable hlocal ha
  match hcases with
  | Or.inl hzero_case =>
      have hvalue_a :
          value a =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaRectangle_zeroPoleResidue f :=
        Eq.subst
          (motive := fun z : ℂ =>
            value z =
              (2 * ↑Real.pi * Complex.I : ℂ) •
                explicitFormulaRectangle_zeroPoleResidue f)
          hzero_case.1.symm
          hvalue_zero
      exact Eq.trans hzero_case.2 hvalue_a.symm
  | Or.inr hnot_zero =>
      match hnot_zero with
      | Or.inl hone_case =>
          have hvalue_a :
              value a =
                (2 * ↑Real.pi * Complex.I : ℂ) •
                  explicitFormulaRectangle_onePoleResidue f :=
            Eq.subst
              (motive := fun z : ℂ =>
                value z =
                  (2 * ↑Real.pi * Complex.I : ℂ) •
                    explicitFormulaRectangle_onePoleResidue f)
              hone_case.1.symm
              hvalue_one
          exact Eq.trans hone_case.2 hvalue_a.symm
      | Or.inr hcompleted_case =>
          match hcompleted_case with
          | ⟨ρ, hρ, hcoord, hcircle⟩ =>
              have hvalue_a :
                  value a =
                    (2 * ↑Real.pi * Complex.I : ℂ) •
                      explicitFormulaZeroResidue f
                        (explicitFormulaZeroDataOfCompletedZero ρ) :=
                Eq.subst
                  (motive := fun z : ℂ =>
                    value z =
                      (2 * ↑Real.pi * Complex.I : ℂ) •
                        explicitFormulaZeroResidue f
                          (explicitFormulaZeroDataOfCompletedZero ρ))
                  hcoord
                  (hvalue_completed ρ hρ)
              exact Eq.trans hcircle hvalue_a.symm

/-- Half-radius family form of the raw deleted-circle common-value supplier.  Its
conclusion is the `hcircle` hypothesis used by the endpoint-data common-value residue
consumer. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_commonValue_on_rawSingularCoordinates
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ) (value : ℝ → ℂ → ℂ)
    (hvalue_zero :
      ∀ ε : ℝ,
        value ε 0 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_zeroPoleResidue f)
    (hvalue_one :
      ∀ ε : ℝ,
        value ε 1 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_onePoleResidue f)
    (hvalue_completed :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
            value ε (completedZeroResidueCoordinate ρ) =
              (2 * ↑Real.pi * Complex.I : ℂ) •
                explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))
    (s0 s1 : ℝ → Set ℂ)
    (hs0 : ∀ ε : ℝ, (s0 ε).Countable)
    (hs1 : ∀ ε : ℝ, (s1 ε).Countable)
    (szero : ℝ → {ρ : ℂ // ZetaCompletedZero ρ} → Set ℂ)
    (hszero :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
            (szero ε ρ).Countable)
      (hzero_continuous :
        ∀ ε : ℝ,
          ContinuousOn
            (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall (0 : ℂ) (ε / 2) \ {(0 : ℂ)}))
    (hzero_differentiable :
      ∀ ε : ℝ,
        ∀ z : ℂ,
          z ∈ (Metric.ball (0 : ℂ) (ε / 2) \ {(0 : ℂ)}) \ s0 ε →
              DifferentiableAt ℂ
                (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
                z)
    (hone_continuous :
      ∀ ε : ℝ,
        ContinuousOn
          (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (1 : ℂ) (ε / 2) \ {(1 : ℂ)}))
    (hone_differentiable :
      ∀ ε : ℝ,
        ∀ z : ℂ,
          z ∈ (Metric.ball (1 : ℂ) (ε / 2) \ {(1 : ℂ)}) \ s1 ε →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z)
    (hcompleted_continuous :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
            ContinuousOn
              (fun z : ℂ =>
                (z - completedZeroResidueCoordinate ρ) *
                  zetaCompletedExplicitFormulaContourIntegrand f z)
              (Metric.closedBall (completedZeroResidueCoordinate ρ) (ε / 2) \
                {completedZeroResidueCoordinate ρ}))
    (hcompleted_differentiable :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
            ∀ z : ℂ,
              z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) (ε / 2) \
                  {completedZeroResidueCoordinate ρ}) \ szero ε ρ →
                DifferentiableAt ℂ
                  (fun w : ℂ =>
                    (w - completedZeroResidueCoordinate ρ) *
                      zetaCompletedExplicitFormulaContourIntegrand f w)
                  z)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                value ε a := by
  intro ε hε _hclosed _hsep
  exact
    explicitFormulaRectangleRawDeletedCircleBoundary_eq_commonValue_on_rawSingularCoordinates
      f hPhi T (finiteRectangle_halfRadius_pos hε) (value ε)
      (hvalue_zero ε) (hvalue_one ε) (hvalue_completed ε)
      (s0 ε) (s1 ε) (hs0 ε) (hs1 ε) (szero ε) (hszero ε)
      (hzero_continuous ε) (hzero_differentiable ε)
      (hone_continuous ε) (hone_differentiable ε)
      (hcompleted_continuous ε) (hcompleted_differentiable ε)
      hlocal

/-- The finite raw deleted-circle boundary sum at radius `ε`, over the finite raw
singular-coordinate carrier. -/
noncomputable def explicitFormulaRectangleRawDeletedCircleBoundarySum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) : ℂ :=
  finiteRectangleDeletedCircleBoundarySum
    (explicitFormulaRectangleRawSingularCoordinates T)
    (explicitFormulaRectangleRawDeletedCircleBoundary f ε)

/-- The finite raw deleted-square boundary sum at radius `ε`, over the finite raw
singular-coordinate carrier. -/
noncomputable def explicitFormulaRectangleRawDeletedSquareBoundarySum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) : ℂ :=
  finiteRectangleDeletedCircleBoundarySum
    (explicitFormulaRectangleRawSingularCoordinates T)
    (explicitFormulaRectangleRawDeletedSquareBoundary f ε)

/-- The finite raw inscribed-square boundary sum at circular radius `ε`, over the finite
raw singular-coordinate carrier. -/
noncomputable def explicitFormulaRectangleRawInscribedSquareBoundarySum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) : ℂ :=
  finiteRectangleDeletedCircleBoundarySum
    (explicitFormulaRectangleRawSingularCoordinates T)
    (explicitFormulaRectangleRawInscribedSquareBoundary f ε)

/-- The finite raw deleted-square boundary sum is the finite carrier sum of the raw
deleted-square boundary function. -/
theorem explicitFormulaRectangleRawDeletedSquareBoundarySum_eq
    (f : ZetaAdmissibleFunction) (T ε : ℝ) :
    explicitFormulaRectangleRawDeletedSquareBoundarySum f T ε =
      finiteRectangleDeletedCircleBoundarySum
        (explicitFormulaRectangleRawSingularCoordinates T)
        (explicitFormulaRectangleRawDeletedSquareBoundary f ε) := by
  exact Eq.refl _

/-- The finite raw deleted-square boundary sum is the finite sum of the
corresponding square subdivision-cell boundaries over the raw singular-coordinate
carrier. -/
theorem explicitFormulaRectangleRawDeletedSquareBoundarySum_eq_cellBoundarySum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) :
    explicitFormulaRectangleRawDeletedSquareBoundarySum f T ε =
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        finiteRectangleSubdivisionCellBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          (finiteRectangleSquareLowerCorner a ε)
          (finiteRectangleSquareUpperCorner a ε) := by
  calc
    explicitFormulaRectangleRawDeletedSquareBoundarySum f T ε =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawDeletedSquareBoundary f ε) := by
      exact explicitFormulaRectangleRawDeletedSquareBoundarySum_eq f T ε
    _ =
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        finiteRectangleSubdivisionCellBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          (finiteRectangleSquareLowerCorner a ε)
          (finiteRectangleSquareUpperCorner a ε) := by
      exact Finset.sum_congr (Eq.refl _)
        (fun a _ha =>
          explicitFormulaRectangleRawDeletedSquareBoundary_eq_cellBoundary f ε a)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
