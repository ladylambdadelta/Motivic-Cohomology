import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part03

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

/-- The local residue contribution of the raw completed contour integrand at the
completed-zeta pole coordinate `0`, in the explicit-formula normalization. -/
noncomputable def explicitFormulaRectangle_zeroPoleResidue
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))

/-- The local residue contribution of the raw completed contour integrand at the
completed-zeta pole coordinate `1`, in the explicit-formula normalization. -/
noncomputable def explicitFormulaRectangle_onePoleResidue
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)

/-- The shifted completed explicit-formula transform tends to its shifted value at any
punctured-neighborhood center. -/
theorem zetaCompletedExplicitFormulaPhi_shift_tendsto_at
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) (a : ℂ) :
    Tendsto
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
      (𝓝[≠] a)
      (𝓝 (zetaCompletedExplicitFormulaPhi f (a - 1 / 2))) := by
  have hcontinuous :
      ContinuousAt
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        a :=
    (zetaCompletedExplicitFormulaPhi_shift_differentiableAt hPhi a).continuousAt
  exact hcontinuous.tendsto.mono_left nhdsWithin_le_nhds

/-- The punctured local-residue coefficient factors into the completed negative
log-derivative coefficient times the shifted test transform. -/
theorem explicitFormulaRectangle_completedZero_localResidue_coeff_factorization
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) (z : ℂ) :
    (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z =
      ((z - completedZeroResidueCoordinate ρ) * completedZetaNegLogDeriv z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2) := by
  exact
    Eq.trans
      (congrArg
        (fun w : ℂ => (z - completedZeroResidueCoordinate ρ) * w)
        (zetaCompletedExplicitFormulaContourIntegrand_eq f z))
      (mul_assoc
        (z - completedZeroResidueCoordinate ρ)
        (completedZetaNegLogDeriv z)
        (zetaCompletedExplicitFormulaPhi f (z - 1 / 2))).symm

/-- The punctured local-residue coefficient at the completed-zeta pole `0` factors into
the completed negative log-derivative coefficient times the shifted test transform. -/
theorem explicitFormulaRectangle_zeroPole_localResidue_coeff_factorization
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    z * zetaCompletedExplicitFormulaContourIntegrand f z =
      (z * completedZetaNegLogDeriv z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2) := by
  exact
    Eq.trans
      (congrArg
        (fun w : ℂ => z * w)
        (zetaCompletedExplicitFormulaContourIntegrand_eq f z))
      (mul_assoc
        z
        (completedZetaNegLogDeriv z)
        (zetaCompletedExplicitFormulaPhi f (z - 1 / 2))).symm

/-- The punctured local-residue coefficient at the completed-zeta pole `1` factors into
the completed negative log-derivative coefficient times the shifted test transform. -/
theorem explicitFormulaRectangle_onePole_localResidue_coeff_factorization
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z =
      ((z - 1) * completedZetaNegLogDeriv z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2) := by
  exact
    Eq.trans
      (congrArg
        (fun w : ℂ => (z - 1) * w)
        (zetaCompletedExplicitFormulaContourIntegrand_eq f z))
      (mul_assoc
        (z - 1)
        (completedZetaNegLogDeriv z)
        (zetaCompletedExplicitFormulaPhi f (z - 1 / 2))).symm

/-- The explicit-formula zero datum at the true uncentered contour pole attached to a
completed zero. -/
noncomputable def explicitFormulaContourZeroDataOfCompletedZero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ExplicitFormulaZeroData :=
  explicitFormulaZeroDataOfCompletedZero ρ

/-- The shifted value of the contour zero datum is the centered completed-zero coordinate. -/
theorem explicitFormulaContourZeroDataOfCompletedZero_zero_sub_half
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (explicitFormulaContourZeroDataOfCompletedZero ρ).zero - (1 / 2 : ℂ) =
      (ρ : ℂ) := by
  unfold explicitFormulaContourZeroDataOfCompletedZero
  exact completedZeroResidueCoordinate_sub_half ρ

/-- The contour alias has the same shifted coordinate as the owner datum. -/
theorem explicitFormulaContourZeroDataOfCompletedZero_zero_sub_half_eq_owner
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (explicitFormulaContourZeroDataOfCompletedZero ρ).zero - (1 / 2 : ℂ) =
      completedZeroResidueCoordinate ρ - (1 / 2 : ℂ) := by
  rfl

/-- The contour-coordinate datum evaluates the test transform at the centered zero
coordinate `ρ`. -/
theorem explicitFormulaContourZeroDataOfCompletedZero_residue_unfold
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ) =
      - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
        zetaCompletedExplicitFormulaPhi f (ρ : ℂ) := by
  have hcoord :
      completedZeroResidueCoordinate ρ - (1 / 2 : ℂ) = (ρ : ℂ) := by
    unfold completedZeroResidueCoordinate
    exact add_sub_cancel_left (1 / 2 : ℂ) (ρ : ℂ)
  exact
    Eq.trans
      (explicitFormulaZeroResidue_def f (explicitFormulaContourZeroDataOfCompletedZero ρ))
      (congrArg
        (fun w : ℂ =>
          -((explicitFormulaContourZeroDataOfCompletedZero ρ).multiplicity : ℂ) *
            zetaCompletedExplicitFormulaPhi f w)
        hcoord)

/-- The contour-coordinate datum uses the true uncentered pole of the rectangle
integrand. -/
theorem explicitFormulaContourZeroDataOfCompletedZero_zero_eq_residueCoordinate
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (explicitFormulaContourZeroDataOfCompletedZero ρ).zero =
      completedZeroResidueCoordinate ρ := by
  rfl

/-- The imported completed-zero datum uses the true uncentered residue coordinate. -/
theorem explicitFormulaZeroDataOfCompletedZero_zero_eq_residueCoordinate
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (explicitFormulaZeroDataOfCompletedZero ρ).zero =
      completedZeroResidueCoordinate ρ := by
  rfl

/-- The completed-zero datum evaluates the test transform at the centered completed-zero
coordinate `ρ`. -/
theorem explicitFormulaZeroDataOfCompletedZero_residue_unfold
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) =
      - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
        zetaCompletedExplicitFormulaPhi f (ρ : ℂ) := by
  exact explicitFormulaZeroResidue_ofCompletedZero_unfold f ρ

/-- The contour-coordinate residue is exactly the local residue target at the true
uncentered pole. -/
theorem explicitFormulaRectangle_completedZero_localResidue_targetCoordinate
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ)) *
        zetaCompletedExplicitFormulaPhi f (completedZeroResidueCoordinate ρ - 1 / 2) =
      explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ) := by
  rfl

/-- The `0` pole residue target in the full-contour product transport. -/
theorem explicitFormulaRectangle_zeroPole_localResidue_targetCoordinate
    (f : ZetaAdmissibleFunction) :
    (1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2) =
      explicitFormulaRectangle_zeroPoleResidue f := by
  have hshift : (0 : ℂ) - 1 / 2 = -(1 / 2 : ℂ) :=
    zero_sub (1 / 2 : ℂ)
  calc
    (1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2) =
        (1 : ℂ) * zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) := by
      exact congrArg
        (fun z : ℂ => (1 : ℂ) * zetaCompletedExplicitFormulaPhi f z)
        hshift
    _ = zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) := by
      exact one_mul (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))
    _ = explicitFormulaRectangle_zeroPoleResidue f := by
      rfl

/-- The `1` pole residue target in the full-contour product transport. -/
theorem explicitFormulaRectangle_onePole_localResidue_targetCoordinate
    (f : ZetaAdmissibleFunction) :
    (1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((1 : ℂ) - 1 / 2) =
      explicitFormulaRectangle_onePoleResidue f := by
  have hshift : (1 : ℂ) - 1 / 2 = 1 / 2 :=
    sub_eq_iff_eq_add.mpr (add_halves (1 : ℂ)).symm
  calc
    (1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((1 : ℂ) - 1 / 2) =
        (1 : ℂ) * zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ) := by
      exact congrArg
        (fun z : ℂ => (1 : ℂ) * zetaCompletedExplicitFormulaPhi f z)
        hshift
    _ = zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ) := by
      exact one_mul (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))
    _ = explicitFormulaRectangle_onePoleResidue f := by
      rfl

/-- Product transport for the full completed explicit-formula integrand at the
completed-zeta pole coordinate `0`.  The only analytic input left exposed here is the
true completed negative log-derivative pole coefficient limit. -/
theorem explicitFormulaRectangle_zeroPole_localResidue_productTransport
    (f : ZetaAdmissibleFunction)
    (hlog :
      Tendsto
        (fun z : ℂ => z * completedZetaNegLogDeriv z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (1 : ℂ)))
    (hphi :
      Tendsto
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (0 : ℂ))
        (𝓝 (zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2)))) :
    Tendsto
      (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (explicitFormulaRectangle_zeroPoleResidue f)) := by
  let rawCoeff : ℂ → ℂ :=
    fun z : ℂ =>
      (z * completedZetaNegLogDeriv z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2)
  let contourCoeff : ℂ → ℂ :=
    fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z
  have hproduct :
      Tendsto rawCoeff (𝓝[≠] (0 : ℂ))
        (𝓝 ((1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))) :=
    hlog.mul hphi
  have hcoeff : contourCoeff = rawCoeff := by
    funext z
    exact explicitFormulaRectangle_zeroPole_localResidue_coeff_factorization f z
  have htarget :
      (1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2) =
        explicitFormulaRectangle_zeroPoleResidue f :=
    explicitFormulaRectangle_zeroPole_localResidue_targetCoordinate f
  have hcontour :
      Tendsto contourCoeff (𝓝[≠] (0 : ℂ))
        (𝓝 ((1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))) :=
    Eq.subst
      (motive := fun ψ : ℂ → ℂ =>
        Tendsto ψ (𝓝[≠] (0 : ℂ))
          (𝓝 ((1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((0 : ℂ) - 1 / 2))))
      hcoeff.symm
      hproduct
  exact
    Eq.subst
      (motive := fun w : ℂ =>
        Tendsto contourCoeff (𝓝[≠] (0 : ℂ)) (𝓝 w))
      htarget
      hcontour

/-- Product transport for the full completed explicit-formula integrand at the
completed-zeta pole coordinate `1`.  The only analytic input left exposed here is the
true completed negative log-derivative pole coefficient limit. -/
theorem explicitFormulaRectangle_onePole_localResidue_productTransport
    (f : ZetaAdmissibleFunction)
    (hlog :
      Tendsto
        (fun z : ℂ => (z - 1) * completedZetaNegLogDeriv z)
        (𝓝[≠] (1 : ℂ))
        (𝓝 (1 : ℂ)))
    (hphi :
      Tendsto
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (1 : ℂ))
        (𝓝 (zetaCompletedExplicitFormulaPhi f ((1 : ℂ) - 1 / 2)))) :
    Tendsto
      (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (explicitFormulaRectangle_onePoleResidue f)) := by
  let rawCoeff : ℂ → ℂ :=
    fun z : ℂ =>
      ((z - 1) * completedZetaNegLogDeriv z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2)
  let contourCoeff : ℂ → ℂ :=
    fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z
  have hproduct :
      Tendsto rawCoeff (𝓝[≠] (1 : ℂ))
        (𝓝 ((1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((1 : ℂ) - 1 / 2))) :=
    hlog.mul hphi
  have hcoeff : contourCoeff = rawCoeff := by
    funext z
    exact explicitFormulaRectangle_onePole_localResidue_coeff_factorization f z
  have htarget :
      (1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((1 : ℂ) - 1 / 2) =
        explicitFormulaRectangle_onePoleResidue f :=
    explicitFormulaRectangle_onePole_localResidue_targetCoordinate f
  have hcontour :
      Tendsto contourCoeff (𝓝[≠] (1 : ℂ))
        (𝓝 ((1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((1 : ℂ) - 1 / 2))) :=
    Eq.subst
      (motive := fun ψ : ℂ → ℂ =>
        Tendsto ψ (𝓝[≠] (1 : ℂ))
          (𝓝 ((1 : ℂ) * zetaCompletedExplicitFormulaPhi f ((1 : ℂ) - 1 / 2))))
      hcoeff.symm
      hproduct
  exact
    Eq.subst
      (motive := fun w : ℂ =>
        Tendsto contourCoeff (𝓝[≠] (1 : ℂ)) (𝓝 w))
      htarget
      hcontour

/-- Full-contour local residue at `0` from the completed negative log-derivative pole
coefficient limit and the analytic-control package for `Φ_f`. -/
theorem explicitFormulaRectangle_zeroPole_localResidue_tendsto_of_completedNegLogDeriv
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (hlog :
      Tendsto
        (fun z : ℂ => z * completedZetaNegLogDeriv z)
        (𝓝[≠] (0 : ℂ))
        (𝓝 (1 : ℂ))) :
    Tendsto
      (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (explicitFormulaRectangle_zeroPoleResidue f)) := by
  exact
    explicitFormulaRectangle_zeroPole_localResidue_productTransport
      f
      hlog
      (zetaCompletedExplicitFormulaPhi_shift_tendsto_at f hPhi (0 : ℂ))

/-- Full-contour local residue at `1` from the completed negative log-derivative pole
coefficient limit and the analytic-control package for `Φ_f`. -/
theorem explicitFormulaRectangle_onePole_localResidue_tendsto_of_completedNegLogDeriv
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (hlog :
      Tendsto
        (fun z : ℂ => (z - 1) * completedZetaNegLogDeriv z)
        (𝓝[≠] (1 : ℂ))
        (𝓝 (1 : ℂ))) :
    Tendsto
      (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (explicitFormulaRectangle_onePoleResidue f)) := by
  exact
    explicitFormulaRectangle_onePole_localResidue_productTransport
      f
      hlog
      (zetaCompletedExplicitFormulaPhi_shift_tendsto_at f hPhi (1 : ℂ))

/-- Full-contour local residue at `0` for the raw completed explicit-formula integrand,
using the completed-zeta pole coefficient `+1`. -/
theorem explicitFormulaRectangle_zeroPole_localResidue_tendsto_rawCompleted
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) :
    Tendsto
      (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (explicitFormulaRectangle_zeroPoleResidue f)) := by
  exact
    explicitFormulaRectangle_zeroPole_localResidue_tendsto_of_completedNegLogDeriv
      f hPhi completedZetaNegLogDeriv_zeroPole_residue_tendsto

/-- Full-contour local residue at `1` for the raw completed explicit-formula integrand,
using the completed-zeta pole coefficient `+1`. -/
theorem explicitFormulaRectangle_onePole_localResidue_tendsto_rawCompleted
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f) :
    Tendsto
      (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (explicitFormulaRectangle_onePoleResidue f)) := by
  exact
    explicitFormulaRectangle_onePole_localResidue_tendsto_of_completedNegLogDeriv
      f hPhi completedZetaNegLogDeriv_onePole_residue_tendsto

/-- The contour-coordinate datum is the correct datum for the finite rectangle pole. -/
theorem explicitFormulaRectangle_completedZero_localResidue_centeredResidueCoordinateCorrection
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (explicitFormulaContourZeroDataOfCompletedZero ρ).zero =
      completedZeroResidueCoordinate ρ ∧
    explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ) =
      - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
        zetaCompletedExplicitFormulaPhi f (completedZeroResidueCoordinate ρ - 1 / 2) := by
  exact And.intro
    (explicitFormulaContourZeroDataOfCompletedZero_zero_eq_residueCoordinate ρ)
    (explicitFormulaRectangle_completedZero_localResidue_targetCoordinate f ρ).symm

/-- Residue compatibility data between the true contour-coordinate zero datum and the
completed zero-side datum consumed by the named finite zero sum.

The finite rectangle residue computation gives the contour-coordinate datum.  This lemma
records both unfolded residues at their own coordinates, so the remaining convention
change is visible to the global finite-sum normalization instead of being hidden as a
false local-residue identity. -/
theorem explicitFormulaRectangle_completedZero_localResidue_zeroDataResidueCompatibility
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ) =
        - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
          zetaCompletedExplicitFormulaPhi f (ρ : ℂ) ∧
      explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) =
        - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
          zetaCompletedExplicitFormulaPhi f (ρ : ℂ) := by
  exact And.intro
    (explicitFormulaContourZeroDataOfCompletedZero_residue_unfold f ρ)
    (explicitFormulaZeroDataOfCompletedZero_residue_unfold f ρ)

/-- Multiplying the completed-zeta logarithmic-derivative local residue by the continuous
test transform gives the contour-coordinate residue summand at the true pole. -/
theorem explicitFormulaRectangle_completedZero_localResidue_productTransport_contourCoordinate
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hlog :
      Tendsto
        (fun z : ℂ => (z - completedZeroResidueCoordinate ρ) * completedZetaNegLogDeriv z)
        (𝓝[≠] (completedZeroResidueCoordinate ρ))
        (𝓝 (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ))))
    (hphi :
      Tendsto
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (completedZeroResidueCoordinate ρ))
        (𝓝 (zetaCompletedExplicitFormulaPhi f
          (completedZeroResidueCoordinate ρ - 1 / 2)))) :
    Tendsto
      (fun z : ℂ =>
        (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ))) := by
  let a : ℂ := -(zetaZeroMultiplicity (ρ : ℂ) : ℂ)
  let b : ℂ := zetaCompletedExplicitFormulaPhi f (completedZeroResidueCoordinate ρ - 1 / 2)
  let rawCoeff : ℂ → ℂ :=
    fun z : ℂ => ((z - completedZeroResidueCoordinate ρ) * completedZetaNegLogDeriv z) *
      zetaCompletedExplicitFormulaPhi f (z - 1 / 2)
  let contourCoeff : ℂ → ℂ :=
    fun z : ℂ => (z - completedZeroResidueCoordinate ρ) *
      zetaCompletedExplicitFormulaContourIntegrand f z
  have hproduct :
      Tendsto rawCoeff (𝓝[≠] (completedZeroResidueCoordinate ρ)) (𝓝 (a * b)) := by
    exact hlog.mul hphi
  have hcoeff :
      contourCoeff = rawCoeff := by
    funext z
    exact explicitFormulaRectangle_completedZero_localResidue_coeff_factorization f ρ z
  have htarget :
      a * b = explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ) :=
    explicitFormulaRectangle_completedZero_localResidue_targetCoordinate f ρ
  have hcontour :
      Tendsto contourCoeff (𝓝[≠] (completedZeroResidueCoordinate ρ)) (𝓝 (a * b)) :=
    Eq.subst
      (motive := fun ψ : ℂ → ℂ =>
        Tendsto ψ (𝓝[≠] (completedZeroResidueCoordinate ρ)) (𝓝 (a * b)))
      hcoeff.symm
      hproduct
  exact
    Eq.subst
      (motive := fun w : ℂ =>
        Tendsto contourCoeff (𝓝[≠] (completedZeroResidueCoordinate ρ)) (𝓝 w))
      htarget
      hcontour

/-- Multiplying the completed-zeta logarithmic-derivative local residue by the continuous
test transform gives the contour-coordinate residue summand at the true uncentered pole.

This owner wrapper intentionally stays at `explicitFormulaContourZeroDataOfCompletedZero`:
the finite rectangle pole is `completedZeroResidueCoordinate ρ = 1 / 2 + ρ`, so the local
product transport samples the test transform at
`completedZeroResidueCoordinate ρ - 1 / 2`.  Conversion to the named zero-side datum is a
separate convention-normalization obligation. -/
theorem explicitFormulaRectangle_completedZero_localResidue_productTransport
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hlog :
      Tendsto
        (fun z : ℂ => (z - completedZeroResidueCoordinate ρ) * completedZetaNegLogDeriv z)
        (𝓝[≠] (completedZeroResidueCoordinate ρ))
        (𝓝 (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ))))
    (hphi :
      Tendsto
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
        (𝓝[≠] (completedZeroResidueCoordinate ρ))
        (𝓝 (zetaCompletedExplicitFormulaPhi f
          (completedZeroResidueCoordinate ρ - 1 / 2)))) :
    Tendsto
      (fun z : ℂ =>
        (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ))) := by
  exact
    explicitFormulaRectangle_completedZero_localResidue_productTransport_contourCoordinate
      f ρ hlog hphi

/-- The local residue of the completed explicit-formula integrand at a completed zero is the
contour-coordinate residue summand, expressed as the punctured-neighborhood coefficient of
the simple-pole part at the true uncentered pole. -/
theorem explicitFormulaRectangle_completedZero_localResidue_tendsto_contourSummand
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    Tendsto
      (fun z : ℂ =>
        (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ))) := by
  exact
    explicitFormulaRectangle_completedZero_localResidue_productTransport_contourCoordinate
      f ρ
      (completedZetaNegLogDeriv_completedZero_residue_tendsto ρ)
      (zetaCompletedExplicitFormulaPhi_completedZero_shift_tendsto f hPhi ρ)

/-- The local residue of the completed explicit-formula integrand at a completed zero is the
named zero-side residue summand only after the centered residue-coordinate correction has
been supplied. -/
theorem explicitFormulaRectangle_completedZero_localResidue_tendsto_summand
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hnormalize :
      explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ) =
        explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) :
    Tendsto
      (fun z : ℂ =>
        (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))) := by
  exact
    Eq.subst
      (motive := fun w : ℂ =>
        Tendsto
          (fun z : ℂ =>
            (z - completedZeroResidueCoordinate ρ) *
              zetaCompletedExplicitFormulaContourIntegrand f z)
          (𝓝[≠] (completedZeroResidueCoordinate ρ))
          (𝓝 w))
      hnormalize
      (explicitFormulaRectangle_completedZero_localResidue_productTransport
        f ρ
        (completedZetaNegLogDeriv_completedZero_residue_tendsto ρ)
        (zetaCompletedExplicitFormulaPhi_completedZero_shift_tendsto f hPhi ρ))

/-- The local Cauchy-residue hypothesis must stay at the true uncentered contour pole.

The older centered-neighborhood surface asked for a punctured neighborhood of `ρ`; that
would move the residue away from the actual pole of the contour integrand.  The corrected
owner statement records that the local theorem supplied at `1 / 2 + ρ` is already in the
coordinate required by the rectangle residue calculation. -/
theorem explicitFormulaRectangle_completedZero_localResidue_zeroSideCoordinateCompatibility_uncenteredPoleTransport
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hlocal :
      Tendsto
        (fun z : ℂ =>
          (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (𝓝[≠] (completedZeroResidueCoordinate ρ))
        (𝓝 (explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ)))) :
    Tendsto
      (fun z : ℂ =>
        (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ))) := by
  exact hlocal

/-- Compatibility sink for consumers that still need the named zero-side residue summand
after the local contour-coordinate residue has been computed.

The named completed-zero datum is now the contour-coordinate datum, so both unfolded
residue presentations sample `Φ_f ρ`. -/
theorem explicitFormulaRectangle_completedZero_localResidue_zeroSideConventionNormalization
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ) =
        - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
          zetaCompletedExplicitFormulaPhi f (ρ : ℂ) ∧
      explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) =
        - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
          zetaCompletedExplicitFormulaPhi f (ρ : ℂ) := by
  exact
    explicitFormulaRectangle_completedZero_localResidue_zeroDataResidueCompatibility
      f ρ

/-- Finite-window convention bridge from the contour-coordinate residue summand to the
named completed-zero residue summand. -/
theorem explicitFormulaRectangle_completedZeroResidueWindow_contourToZeroSideConvention
    (f : ZetaAdmissibleFunction) (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (_hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T) :
    explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ) =
        - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
          zetaCompletedExplicitFormulaPhi f (ρ : ℂ) ∧
      explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) =
        - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
          zetaCompletedExplicitFormulaPhi f (ρ : ℂ) := by
  exact
    explicitFormulaRectangle_completedZero_localResidue_zeroSideConventionNormalization
      f ρ

/-- The contour datum and named completed-zero datum have the same `Φ` argument. -/
theorem explicitFormulaRectangle_completedZeroResidueWindow_phiConventionCorrection
    (f : ZetaAdmissibleFunction) (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (_hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T) :
    zetaCompletedExplicitFormulaPhi f (ρ : ℂ) =
      zetaCompletedExplicitFormulaPhi f (ρ : ℂ) := by
  rfl

/-- The contour datum and named completed-zero datum produce the same residue summand. -/
theorem explicitFormulaRectangle_completedZeroResidueWindow_contourToZeroSideResidueEquality
    (f : ZetaAdmissibleFunction) (T : ℝ)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (_hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T)
    (hphi :
      zetaCompletedExplicitFormulaPhi f (ρ : ℂ) =
        zetaCompletedExplicitFormulaPhi f (ρ : ℂ)) :
    explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ) =
      explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) := by
  calc
    explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ)
        = - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
            zetaCompletedExplicitFormulaPhi f (ρ : ℂ) := by
          exact explicitFormulaContourZeroDataOfCompletedZero_residue_unfold f ρ
    _ = - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) *
          zetaCompletedExplicitFormulaPhi f (ρ : ℂ) := by
          exact
            congrArg
              (fun value : ℂ =>
                - (zetaZeroMultiplicity (ρ : ℂ) : ℂ) * value)
              hphi
    _ = explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) := by
          exact (explicitFormulaZeroDataOfCompletedZero_residue_unfold f ρ).symm

/-- Transport the already-computed local residue at the true uncentered contour pole to
the currently named zero-side summand through the explicit convention-normalization leaf. -/
theorem explicitFormulaRectangle_completedZero_localResidue_zeroSideCoordinateCompatibility_from_uncentered
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hnormalize :
      explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ) =
        explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))
    (hlocal :
      Tendsto
        (fun z : ℂ =>
          (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (𝓝[≠] (completedZeroResidueCoordinate ρ))
        (𝓝 (explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ)))) :
    Tendsto
      (fun z : ℂ =>
        (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))) := by
  have hcontour :
      Tendsto
        (fun z : ℂ =>
          (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (𝓝[≠] (completedZeroResidueCoordinate ρ))
        (𝓝 (explicitFormulaZeroResidue f (explicitFormulaContourZeroDataOfCompletedZero ρ))) :=
    explicitFormulaRectangle_completedZero_localResidue_zeroSideCoordinateCompatibility_uncenteredPoleTransport
      f ρ hlocal
  exact
    Eq.subst
      (motive := fun w : ℂ =>
        Tendsto
          (fun z : ℂ =>
            (z - completedZeroResidueCoordinate ρ) *
              zetaCompletedExplicitFormulaContourIntegrand f z)
          (𝓝[≠] (completedZeroResidueCoordinate ρ))
          (𝓝 w))
      hnormalize
      hcontour

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
