import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part28

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

/-- Square-hole replacement form of the finite-radius tangent punctured-boundary zero:
if the square-deleted punctured boundary vanishes and each square deleted boundary agrees
with the corresponding circular deleted boundary on the finite raw singular carrier, then
the public circular-hole punctured boundary vanishes. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_rawDeletedSquareBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hsquareZero :
      explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T ε = 0)
    (hsquare :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f ε a =
            explicitFormulaRectangleRawDeletedSquareBoundary f ε a) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundary_eq_on
    f F T ε
    (explicitFormulaRectangleRawDeletedSquareBoundary f ε)
    hsquareZero
    hsquare

/-- Inscribed-square replacement form of the finite-radius tangent punctured-boundary zero:
if the inscribed-square-deleted punctured boundary vanishes and each inscribed-square
deleted boundary agrees with the corresponding circular deleted boundary on the finite raw
singular carrier, then the public circular-hole punctured boundary vanishes. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_rawInscribedSquareBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hsquareZero :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε = 0)
    (hsquare :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f ε a =
            explicitFormulaRectangleRawInscribedSquareBoundary f ε a) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundary_eq_on
    f F T ε
    (explicitFormulaRectangleRawInscribedSquareBoundary f ε)
    hsquareZero
    hsquare

/-- Circle-to-inscribed-square deleted-boundary transport in public tangent punctured-boundary
form: equality of each raw deleted boundary value transports the zero of the
inscribed-square punctured boundary to the circular punctured boundary at the same
radius. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_rawInscribedSquareBoundary_transport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hsquareZero :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε = 0)
    (hdeleted :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f ε a =
            explicitFormulaRectangleRawInscribedSquareBoundary f ε a) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε = 0 := by
  have hsum :
      explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε =
        explicitFormulaRectangleRawInscribedSquareBoundarySum f T ε :=
    explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_rawInscribedSquareBoundarySum_of_boundary_eq_on
      f T ε hdeleted
  have hsquarePunctured :
      explicitFormulaRectangleTangentPuncturedBoundaryIntegral f F T
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawInscribedSquareBoundary f ε) = 0 := by
    exact hsquareZero
  exact
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundarySum_eq
      f F T ε
      (explicitFormulaRectangleRawInscribedSquareBoundary f ε)
      hsquarePunctured
      hsum

/-- Half-width deleted-square replacement form of the finite-radius tangent
punctured-boundary zero. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_half_eq_zero_of_rawDeletedSquareBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hsquareZero :
      explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T (ε / 2) = 0)
    (hsquare :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
            explicitFormulaRectangleRawDeletedSquareBoundary f (ε / 2) a) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
      f F T (ε / 2) = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_rawDeletedSquareBoundary
    f F T (ε / 2) hsquareZero hsquare

/-- Half-width circular punctured-boundary transport from an inscribed-square
Cauchy zero through the deleted-square normalization. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_half_eq_zero_of_rawInscribedSquareBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hinscribedZero :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε = 0)
    (hsquare :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
            explicitFormulaRectangleRawDeletedSquareBoundary f (ε / 2) a) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
      f F T (ε / 2) = 0 := by
  have hsquareZero :
      explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral
        f F T (ε / 2) = 0 :=
    explicitFormulaRectangleTangentFiniteRadiusSquarePuncturedBoundaryIntegral_half_eq_zero_of_inscribedSquarePuncturedBoundary
      f F T ε hinscribedZero
  exact
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_half_eq_zero_of_rawDeletedSquareBoundary
      f F T ε hsquareZero hsquare

/-- If the completed explicit-formula finite punctured rectangle has zero tangent boundary
integral, then the tangent outer rectangle contour equals the finite deleted-circle
boundary sum in positive residue orientation. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_deletedCircleBoundarySum_of_tangentPuncturedBoundaryIntegral_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (S : Finset ℂ) (deletedCircle : ℂ → ℂ)
    (hcauchy :
      explicitFormulaRectangleTangentPuncturedBoundaryIntegral f F T S deletedCircle = 0) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      finiteRectangleDeletedCircleBoundarySum S deletedCircle := by
  exact
    finiteRectangle_outerBoundary_eq_deletedCircleBoundarySum_of_puncturedBoundaryIntegral_zero
      S
      (zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T))
      deletedCircle
      hcauchy

/-- The residue-theorem normalization constant `2πi` is nonzero. -/
theorem finiteRectangle_twoPiI_ne_zero :
    (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (two_ne_zero : (2 : ℝ) ≠ 0))
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- Limit form of the same punctured-rectangle boundary accounting.  This is the bridge
between a shrinking punctured-rectangle Cauchy identity and the deleted-circle residue
limits. -/
theorem finiteRectangle_outerBoundary_tendsto_deletedCircleBoundarySum_of_puncturedBoundary
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι}
    (outer : ι → ℂ) (deletedCircleSum : ι → ℂ)
    (puncturedBoundary : ι → ℂ)
    (residueSum : ℂ)
    (hdecomp :
      ∀ i : ι, puncturedBoundary i = outer i - deletedCircleSum i)
    (hcauchy : Tendsto puncturedBoundary l (𝓝 0))
    (hdeleted : Tendsto deletedCircleSum l (𝓝 residueSum)) :
    Tendsto outer l (𝓝 residueSum) := by
  have hcauchy' :
      Tendsto (fun i : ι => outer i - deletedCircleSum i) l (𝓝 0) := by
    exact hcauchy.congr'
      (Filter.Eventually.of_forall
        (fun i => hdecomp i))
  exact
    finiteRectangleResidueAccounting_tendsto_of_puncturedCauchy_and_deletedBoundary
      outer deletedCircleSum residueSum hcauchy' hdeleted

/-- The finite deleted-circle boundary sum tends to the finite residue sum when each
positively oriented deleted-circle contribution tends to its local residue. -/
theorem finiteRectangleDeletedCircleBoundarySum_tendsto_residueSum_of_local
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι}
    (S : Finset ℂ) (deletedCircle : ι → ℂ → ℂ) (residue : ℂ → ℂ)
    (hlocal :
      ∀ a : ℂ, a ∈ S →
        Tendsto (fun i : ι => deletedCircle i a) l (𝓝 (residue a))) :
    Tendsto
      (fun i : ι =>
        finiteRectangleDeletedCircleBoundarySum S (deletedCircle i))
      l
      (𝓝 (∑ a in S, residue a)) := by
  exact
    finiteRectangleDeletedBoundary_tendsto_sum_of_local
      S deletedCircle residue hlocal

/-- Completed-zero deleted-circle boundary contributions over the height window tend to
the completed-zero residue window. -/
theorem explicitFormulaRectangle_completedZeroDeletedCircleBoundarySum_tendsto_residueWindow
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι}
    (f : ZetaAdmissibleFunction) (T : ℝ)
    (deletedCircle : ι → {ρ : ℂ // ZetaCompletedZero ρ} → ℂ)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun i : ι => deletedCircle i ρ)
            l
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    Tendsto
      (fun i : ι =>
        ∑ ρ in explicitFormulaCompletedZeroHeightWindow T, deletedCircle i ρ)
      l
      (𝓝 (explicitFormulaCompletedZeroHeightWindowResidueSum f T)) := by
  have hsum :
      Tendsto
        (fun i : ι =>
          ∑ ρ in explicitFormulaCompletedZeroHeightWindow T, deletedCircle i ρ)
        l
        (𝓝
          (∑ ρ in explicitFormulaCompletedZeroHeightWindow T,
            explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))) :=
    explicitFormulaRectangle_completedZeroDeletedBoundary_tendsto_residueWindowSum
      f T deletedCircle hlocal
  have htarget :
      (∑ ρ in explicitFormulaCompletedZeroHeightWindow T,
        explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T :=
    explicitFormulaRectangle_completedZeroResidueWindowSum_eq_heightWindowResidueSum f T
  exact htarget ▸ hsum

/-- Tangent punctured-rectangle residue assembly for the raw singular coordinate carrier,
with Mathlib's raw circle-integral normalization.

Once Cauchy-Goursat gives zero on the tangent punctured boundary, and the deleted-circle
boundary sum has been evaluated as `2πi` times the indexed raw singular residue sum, the
tangent outer rectangle contour has the corresponding `2πi`-scaled pole-corrected residue
target. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_tangentPuncturedBoundary_and_rawDeletedCircleSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (deletedCircle : ℂ → ℂ)
    (hcauchy :
      explicitFormulaRectangleTangentPuncturedBoundaryIntegral f F T
        (explicitFormulaRectangleRawSingularCoordinates T) deletedCircle = 0)
    (hdeleted :
      finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T) deletedCircle =
        (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangleRawSingularIndexedResidueSum f T) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have houter :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T) deletedCircle :=
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_deletedCircleBoundarySum_of_tangentPuncturedBoundaryIntegral_zero
      f F T (explicitFormulaRectangleRawSingularCoordinates T) deletedCircle hcauchy
  calc
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T) deletedCircle := by
      exact houter
    _ = (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangleRawSingularIndexedResidueSum f T := by
      exact hdeleted
    _ = (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
      exact congrArg
        (fun x : ℂ => (2 * ↑Real.pi * Complex.I : ℂ) • x)
        (explicitFormulaRectangleRawSingularIndexedResidueSum_eq_poleCorrectedResidueSum
          f T)

/-- Tangent punctured-rectangle residue assembly from local deleted-circle values, in
raw circle-integral normalization.

This is the non-opaque form of the punctured Cauchy bridge: after the geometric
punctured-boundary integral is zero, it remains only to identify the local
deleted-circle values at the two completed-zeta pole coordinates and at each
completed-zero coordinate, each with the `2πi` circle-integral factor. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_tangentPuncturedBoundary_and_rawDeletedCircleValues
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (deletedCircle : ℂ → ℂ)
    (hcauchy :
      explicitFormulaRectangleTangentPuncturedBoundaryIntegral f F T
        (explicitFormulaRectangleRawSingularCoordinates T) deletedCircle = 0)
    (hzero :
      deletedCircle 0 =
        (2 * ↑Real.pi * Complex.I : ℂ) • explicitFormulaRectangle_zeroPoleResidue f)
    (hone :
      deletedCircle 1 =
        (2 * ↑Real.pi * Complex.I : ℂ) • explicitFormulaRectangle_onePoleResidue f)
    (hcompleted :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T,
          deletedCircle (completedZeroResidueCoordinate ρ) =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  let c : ℂ := (2 * ↑Real.pi * Complex.I : ℂ)
  have hc_ne : c ≠ 0 :=
    finiteRectangle_twoPiI_ne_zero
  let normalizedDeletedCircle : ℂ → ℂ := fun z : ℂ => c⁻¹ • deletedCircle z
  have hzero_normalized :
      normalizedDeletedCircle 0 = explicitFormulaRectangle_zeroPoleResidue f := by
    calc
      normalizedDeletedCircle 0 = c⁻¹ • deletedCircle 0 := by
        exact Eq.refl _
      _ = c⁻¹ • (c • explicitFormulaRectangle_zeroPoleResidue f) := by
        exact congrArg (fun x : ℂ => c⁻¹ • x) hzero
      _ = ((c⁻¹ * c : ℂ) • explicitFormulaRectangle_zeroPoleResidue f : ℂ) := by
        show
          c⁻¹ • (c • explicitFormulaRectangle_zeroPoleResidue f) =
            ((c⁻¹ * c : ℂ) • explicitFormulaRectangle_zeroPoleResidue f : ℂ)
        exact smul_smul c⁻¹ c (explicitFormulaRectangle_zeroPoleResidue f)
      _ = ((1 : ℂ) • explicitFormulaRectangle_zeroPoleResidue f : ℂ) := by
        exact congrArg
          (fun x : ℂ => x • explicitFormulaRectangle_zeroPoleResidue f)
          (inv_mul_cancel₀ hc_ne)
      _ = explicitFormulaRectangle_zeroPoleResidue f := by
        exact one_smul ℂ (explicitFormulaRectangle_zeroPoleResidue f)
  have hone_normalized :
      normalizedDeletedCircle 1 = explicitFormulaRectangle_onePoleResidue f := by
    calc
      normalizedDeletedCircle 1 = c⁻¹ • deletedCircle 1 := by
        exact Eq.refl _
      _ = c⁻¹ • (c • explicitFormulaRectangle_onePoleResidue f) := by
        exact congrArg (fun x : ℂ => c⁻¹ • x) hone
      _ = ((c⁻¹ * c : ℂ) • explicitFormulaRectangle_onePoleResidue f : ℂ) := by
        show
          c⁻¹ • (c • explicitFormulaRectangle_onePoleResidue f) =
            ((c⁻¹ * c : ℂ) • explicitFormulaRectangle_onePoleResidue f : ℂ)
        exact smul_smul c⁻¹ c (explicitFormulaRectangle_onePoleResidue f)
      _ = ((1 : ℂ) • explicitFormulaRectangle_onePoleResidue f : ℂ) := by
        exact congrArg
          (fun x : ℂ => x • explicitFormulaRectangle_onePoleResidue f)
          (inv_mul_cancel₀ hc_ne)
      _ = explicitFormulaRectangle_onePoleResidue f := by
        exact one_smul ℂ (explicitFormulaRectangle_onePoleResidue f)
  have hcompleted_normalized :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T,
          normalizedDeletedCircle (completedZeroResidueCoordinate ρ) =
            explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) := by
    intro ρ hρ
    calc
      normalizedDeletedCircle (completedZeroResidueCoordinate ρ) =
          c⁻¹ • deletedCircle (completedZeroResidueCoordinate ρ) := by
        exact Eq.refl _
      _ = c⁻¹ •
            (c •
              explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) := by
        exact congrArg
          (fun x : ℂ => c⁻¹ • x)
          (hcompleted ρ hρ)
      _ = ((c⁻¹ * c : ℂ) •
            explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) : ℂ) := by
        show
          c⁻¹ •
              (c •
                explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) =
            ((c⁻¹ * c : ℂ) •
              explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) : ℂ)
        exact
          smul_smul c⁻¹ c
            (explicitFormulaZeroResidue f
              (explicitFormulaZeroDataOfCompletedZero ρ))
      _ = ((1 : ℂ) •
            explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) : ℂ) := by
        exact congrArg
          (fun x : ℂ =>
            x • explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))
          (inv_mul_cancel₀ hc_ne)
      _ = explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) := by
        exact one_smul ℂ
          (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))
  have hnormalized_deleted :
      finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T) normalizedDeletedCircle =
        explicitFormulaRectangleRawSingularIndexedResidueSum f T :=
    finiteRectangleDeletedCircleBoundarySum_rawSingularCoordinates_eq_indexedResidueSum_of_values
      f T normalizedDeletedCircle hzero_normalized hone_normalized hcompleted_normalized
  have hdeleted :
      finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T) deletedCircle =
        c • explicitFormulaRectangleRawSingularIndexedResidueSum f T := by
    let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
    have hpoint :
        ∀ z : ℂ, z ∈ S → deletedCircle z = c • normalizedDeletedCircle z := by
      intro z _hz
      calc
        deletedCircle z = ((1 : ℂ) • deletedCircle z : ℂ) := by
          exact (one_smul ℂ (deletedCircle z)).symm
        _ = ((c * c⁻¹ : ℂ) • deletedCircle z : ℂ) := by
          exact congrArg
            (fun x : ℂ => x • deletedCircle z)
            (mul_inv_cancel₀ hc_ne).symm
        _ = c • (c⁻¹ • deletedCircle z) := by
          show
            ((c * c⁻¹ : ℂ) • deletedCircle z : ℂ) =
              c • (c⁻¹ • deletedCircle z)
          exact (smul_smul c c⁻¹ (deletedCircle z)).symm
        _ = c • normalizedDeletedCircle z := by
          exact Eq.refl _
    calc
      finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T) deletedCircle =
          ∑ z in S, deletedCircle z := by
        exact Eq.refl _
      _ = ∑ z in S, c • normalizedDeletedCircle z := by
        exact Finset.sum_congr (Eq.refl _) hpoint
      _ = c • ∑ z in S, normalizedDeletedCircle z := by
        exact (Finset.smul_sum).symm
      _ = c •
          finiteRectangleDeletedCircleBoundarySum
            (explicitFormulaRectangleRawSingularCoordinates T)
            normalizedDeletedCircle := by
        exact Eq.refl _
      _ = c • explicitFormulaRectangleRawSingularIndexedResidueSum f T := by
        exact congrArg (fun x : ℂ => c • x) hnormalized_deleted
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_tangentPuncturedBoundary_and_rawDeletedCircleSum
      f F T deletedCircle hcauchy hdeleted

/-- Finite-radius tangent punctured-rectangle residue assembly from the actual raw
deleted-circle boundary integrals.

This is the geometric finite-radius form used by the punctured-rectangle Cauchy
construction.  It does not quantify over an arbitrary deleted-boundary function: the
deleted circles are the actual radius-`ε` circle integrals of the raw completed
explicit-formula integrand. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_rawDeletedCircleValues
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hcauchy :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F T ε = 0)
    (hzero :
      explicitFormulaRectangleRawDeletedCircleBoundary f ε 0 =
        (2 * ↑Real.pi * Complex.I : ℂ) • explicitFormulaRectangle_zeroPoleResidue f)
    (hone :
      explicitFormulaRectangleRawDeletedCircleBoundary f ε 1 =
        (2 * ↑Real.pi * Complex.I : ℂ) • explicitFormulaRectangle_onePoleResidue f)
    (hcompleted :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T,
          explicitFormulaRectangleRawDeletedCircleBoundary f ε
              (completedZeroResidueCoordinate ρ) =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_tangentPuncturedBoundary_and_rawDeletedCircleValues
      f F T
      (explicitFormulaRectangleRawDeletedCircleBoundary f ε)
      hcauchy hzero hone hcompleted

/-- Finite-radius tangent punctured-rectangle residue assembly with the two completed-zeta
pole deleted-circle values supplied by the owner-proved pole coefficient theorem.

After this lemma, the remaining local deleted-circle input is only the completed-zero
window contribution; the `0` and `1` pole circle values are no longer external
assumptions. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_completedZeroDeletedCircleValues
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hPhi : ZetaPhiAnalyticControl f)
    (hε_pos : 0 < ε)
    (s0 s1 : Set ℂ) (hs0 : s0.Countable) (hs1 : s1.Countable)
    (hcauchy :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F T ε = 0)
      (hzero_continuous :
        ContinuousOn
          (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) ε \ {(0 : ℂ)}))
    (hzero_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) ε \ {(0 : ℂ)}) \ s0 →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z)
    (hone_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) ε \ {(1 : ℂ)}))
    (hone_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) ε \ {(1 : ℂ)}) \ s1 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hcompleted :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T,
          explicitFormulaRectangleRawDeletedCircleBoundary f ε
              (completedZeroResidueCoordinate ρ) =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have hzero :
      explicitFormulaRectangleRawDeletedCircleBoundary f ε 0 =
        (2 * ↑Real.pi * Complex.I : ℂ) • explicitFormulaRectangle_zeroPoleResidue f :=
    explicitFormulaRectangleRawDeletedCircleBoundary_zeroPole_eq_twoPiI_smul_residue_of_regular
      f hPhi hε_pos s0 hs0 hzero_continuous hzero_differentiable
  have hone :
      explicitFormulaRectangleRawDeletedCircleBoundary f ε 1 =
        (2 * ↑Real.pi * Complex.I : ℂ) • explicitFormulaRectangle_onePoleResidue f :=
    explicitFormulaRectangleRawDeletedCircleBoundary_onePole_eq_twoPiI_smul_residue_of_regular
      f hPhi hε_pos s1 hs1 hone_continuous hone_differentiable
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_rawDeletedCircleValues
      f F T ε hcauchy hzero hone hcompleted

/-- Finite-radius tangent punctured-rectangle residue assembly from local deleted-disk
regularity at every raw singular coordinate.  The pole circle values are supplied by the
completed-zeta pole coefficient theorem, and each completed-zero circle value is supplied by
the completed-zero local residue limit.  The only geometric input still external here is the
finite-hole Cauchy zero for the chosen radius. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_localRegularity
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hPhi : ZetaPhiAnalyticControl f)
    (hε_pos : 0 < ε)
    (s0 s1 : Set ℂ) (hs0 : s0.Countable) (hs1 : s1.Countable)
    (szero : {ρ : ℂ // ZetaCompletedZero ρ} → Set ℂ)
    (hszero :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          (szero ρ).Countable)
    (hcauchy :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F T ε = 0)
      (hzero_continuous :
        ContinuousOn
          (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) ε \ {(0 : ℂ)}))
    (hzero_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (0 : ℂ) ε \ {(0 : ℂ)}) \ s0 →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z)
    (hone_continuous :
      ContinuousOn
        (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Metric.closedBall (1 : ℂ) ε \ {(1 : ℂ)}))
    (hone_differentiable :
      ∀ z : ℂ,
        z ∈ (Metric.ball (1 : ℂ) ε \ {(1 : ℂ)}) \ s1 →
          DifferentiableAt ℂ
            (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
            z)
    (hcompleted_continuous :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          ContinuousOn
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall (completedZeroResidueCoordinate ρ) ε \
              {completedZeroResidueCoordinate ρ}))
    (hcompleted_differentiable :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T,
          ∀ z : ℂ,
            z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) ε \
                {completedZeroResidueCoordinate ρ}) \ szero ρ →
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  (w - completedZeroResidueCoordinate ρ) *
                    zetaCompletedExplicitFormulaContourIntegrand f w)
                z)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have hcompleted :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T,
          explicitFormulaRectangleRawDeletedCircleBoundary f ε
              (completedZeroResidueCoordinate ρ) =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) :=
    fun ρ hρ =>
      explicitFormulaRectangleRawDeletedCircleBoundary_completedZero_eq_twoPiI_smul_residue
        f T ρ hρ hε_pos (szero ρ) (hszero ρ hρ)
        (hcompleted_continuous ρ hρ)
        (hcompleted_differentiable ρ hρ)
        hlocal
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_completedZeroDeletedCircleValues
      f F T ε hPhi hε_pos s0 s1 hs0 hs1 hcauchy
      hzero_continuous hzero_differentiable
      hone_continuous hone_differentiable
      hcompleted

/-- Finite-radius tangent punctured-rectangle residue assembly from the closed-radius raw
singular-coordinate geometry.  The closed-disk geometry supplies all deleted-circle
regularity inputs; the remaining geometric input is the finite-hole Cauchy zero. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_closedRadiusGeometry
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T ε : ℝ)
    (hT : 0 < T) (hε_pos : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hgeometry :
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)))
    (hcauchy :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F T ε = 0)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  let s : Set ℂ := completedZetaContourIntegrandSingularSet
  have hs : s.Countable :=
    completedZetaContourIntegrandSingularSet_countable
  have hzeroRawReg :
      ContinuousOn
          (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) ε \ {(0 : ℂ)}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball (0 : ℂ) ε \ {(0 : ℂ)}) \ s →
            DifferentiableAt ℂ
              (fun w : ℂ => w * zetaCompletedExplicitFormulaContourIntegrand f w)
              z) :=
    explicitFormulaRectangle_zeroPole_rawDeletedCircle_regular_of_closedRadiusGeometry
      f F h hT hε_pos hinterior hgeometry s
  have hzero_coeff :
      (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z) =
        (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z) := by
    funext z
    exact
      congrArg
        (fun x : ℂ => x * zetaCompletedExplicitFormulaContourIntegrand f z)
        (Eq.symm (sub_zero z))
  have hzeroReg :
      ContinuousOn
          (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) ε \ {(0 : ℂ)}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball (0 : ℂ) ε \ {(0 : ℂ)}) \ s →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z) :=
    And.intro
      (Eq.subst
        (motive := fun g : ℂ → ℂ =>
          ContinuousOn g (Metric.closedBall (0 : ℂ) ε \ {(0 : ℂ)}))
        hzero_coeff
        hzeroRawReg.left)
      (Eq.subst
        (motive := fun g : ℂ → ℂ =>
          ∀ z : ℂ,
            z ∈ (Metric.ball (0 : ℂ) ε \ {(0 : ℂ)}) \ s →
              DifferentiableAt ℂ g z)
        hzero_coeff
        hzeroRawReg.right)
  have honeReg :
      ContinuousOn
          (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (1 : ℂ) ε \ {(1 : ℂ)}) ∧
        (∀ z : ℂ,
          z ∈ (Metric.ball (1 : ℂ) ε \ {(1 : ℂ)}) \ s →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z) :=
    explicitFormulaRectangle_onePole_rawDeletedCircle_regular_of_closedRadiusGeometry
      f F h hT hε_pos hinterior hgeometry s
  have hcompletedReg :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T,
          ContinuousOn
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall (completedZeroResidueCoordinate ρ) ε \
              {completedZeroResidueCoordinate ρ}) ∧
          (∀ z : ℂ,
            z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) ε \
                {completedZeroResidueCoordinate ρ}) \ s →
              DifferentiableAt ℂ
                (fun w : ℂ =>
                  (w - completedZeroResidueCoordinate ρ) *
                    zetaCompletedExplicitFormulaContourIntegrand f w)
                z) :=
    fun ρ hρ =>
      explicitFormulaRectangle_completedZero_rawDeletedCircle_regular_of_closedRadiusGeometry
        f F h hT hε_pos hinterior hgeometry ρ hρ s
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_localRegularity
      f F T ε h.phi_control hε_pos
      s s hs hs
      (fun _ => s)
      (fun ρ hρ => hs)
      hcauchy
      hzeroReg.1 hzeroReg.2
      honeReg.1 honeReg.2
      (fun ρ hρ => (hcompletedReg ρ hρ).1)
      (fun ρ hρ => (hcompletedReg ρ hρ).2)
      hlocal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
