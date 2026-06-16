import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaInteriorCapCollars

/-!
# Finite-hole and small-circle residue accounting for Abel-Plana

This file owns the punctured-rectangle Cauchy transport and the normalized
small-circle contribution limits before endpoint semicircle indentation limits
are assembled.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology


/-- Finite-hole Cauchy-Goursat for the Abel-Plana punctured rectangle, in the
form that consumes only the holomorphicity of the rectangle integrand on the
punctured domain and the geometric deleted-disk separation data.

This theorem is the reusable planar topology owner for the contour proof.  Its
proof is the standard finite-hole argument: cut the punctured rectangle into
ordinary rectangles/strips, apply
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` on each strip,
sum the resulting zero boundary integrals, cancel all internal vertical edges,
and identify the remaining oriented boundary with the named outer
principal-value boundary minus the endpoint and interior deleted arcs. -/
theorem Complex.finiteAbelPlana_log_finiteHoleCauchyGoursat_of_puncturedRectangleHolomorphic
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ =
      0 := by
  have hsubdivision_boundary :
      Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ =
        Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ := by
    exact
      Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_finiteRadiusPuncturedBoundary_public
        N T hρ hdeleted_geometry hcont hdiff
  have hsubdivision_zero :
      Complex.finiteAbelPlanaLogFiniteHoleSubdivisionBoundary N w T ρ = 0 := by
      exact
        Complex.finiteAbelPlana_log_finiteHoleSubdivisionBoundary_eq_zero
        N T hT hρ hdeleted_geometry hcont hdiff
  exact Eq.trans hsubdivision_boundary.symm hsubdivision_zero

/-- Cauchy-Goursat on the finite-radius punctured Abel-Plana rectangle.

This is the remaining analytic-geometric owner step: decompose the punctured
rectangle into ordinary subdomains whose boundaries cancel on internal cuts,
use the endpoint semicircle orientations above for the boundary poles, use
the interior circle orientation from the deleted-boundary decomposition, and
apply Cauchy-Goursat on each subdomain because the deleted disks isolate all
integer cotangent poles. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangle_subdomainCauchyGoursat
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n) :
    Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ =
      0 := by
  have hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_puncturedRectangle
      hw N T hρ
  have hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ) :=
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_puncturedRectangle
      hw N T hρ
  exact
    Complex.finiteAbelPlana_log_finiteHoleCauchyGoursat_of_puncturedRectangleHolomorphic
      N T hT hρ hdeleted_geometry hcont hdiff

/-- Endpoint indentation accounting for the two boundary cotangent poles.

The left and right principal-value indentations around `0` and `N + 1`
contribute the endpoint residue term in the same normalization as the
small-circle residue sum.  This is the boundary-pole part of the principal
value contour theorem; it is separated from the interior finite-hole
calculation so the final Cauchy theorem does not hide endpoint geometry. -/
theorem Complex.finiteAbelPlana_log_endpointBoundaryPoleIndentationAccounting
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T) :
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w -
        Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w =
      0 := by
  dsimp [Complex.finiteAbelPlanaLogEndpointPVIndentationContribution,
    Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution,
    Complex.finiteAbelPlanaLogSummandHalfEndpoints,
    Complex.finiteAbelPlanaLogIntegerResidue,
    Complex.finiteAbelPlanaLogSummand]
  ring

/-- Finite-radius Cauchy-Goursat for the punctured Abel-Plana rectangle.

The poles at `1, ..., N` are interior deleted disks, while the endpoint poles
`0` and `N+1` sit on the vertical boundary and are treated by the same
principal-value indentation convention as the side expressions.  This theorem
owns the planar decomposition/orientation calculation: subdivide the indented
rectangle into ordinary rectangles, cancel internal edges, and identify the
remaining oriented boundary with the normalized outer principal-value boundary
minus the true finite-radius deleted-boundary contribution. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangleCauchy_finiteRadius
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
      Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
      0 := by
  have hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n := by
    exact
      Complex.finiteAbelPlana_log_puncturedRectangle_deletedDiskGeometry
        w N T hρR
  have hboundary :
      Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ =
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ := by
    exact
      Complex.finiteAbelPlana_log_puncturedRectangle_boundaryDecomposition
        N w T ρ
  have hcauchy :
      Complex.finiteAbelPlanaLogFiniteRadiusPuncturedBoundaryIntegral N w T ρ =
        0 := by
    exact
      Complex.finiteAbelPlana_log_puncturedRectangle_subdomainCauchyGoursat
        hw N T hT hρ hdeleted_geometry
  exact Eq.trans hboundary.symm hcauchy

/-- Principal-value Cauchy-Goursat for the finite Abel-Plana rectangle with
integer cotangent poles. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangle_principalValueBoundaryPoleCauchy
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
      Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
      0 := by
  exact
    Complex.finiteAbelPlana_log_puncturedRectangleCauchy_finiteRadius
      hw N T hT hρ hρR

/-- Cauchy-Goursat applied to the finite principal-value rectangle, with the
oriented boundary identified as the normalized outer rectangle contribution
minus the principal-value small-circle contribution. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangle_cauchyBoundary
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
      0 := by
  exact
    Complex.finiteAbelPlana_log_puncturedRectangle_principalValueBoundaryPoleCauchy
      hw N T hT hρ hρR

/-- Boundary orientation accounting for the punctured finite Abel-Plana
rectangle.

This theorem owns the geometric bookkeeping: the oriented boundary of the
rectangle with the pole-disks removed is the outer rectangle boundary minus
the normalized small-circle boundaries. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangle_boundaryAccounting
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
      0 := by
  exact
    Complex.finiteAbelPlana_log_puncturedRectangle_cauchyBoundary
      hw N T hT hρ hρR

/-- The punctured finite Abel-Plana rectangle has zero normalized boundary
integral for every sufficiently small deletion radius. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangleBoundary_eq_zero_of_pos_lt_radiusBound
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρR : ρ <
      Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T) :
    Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
        Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
      0 := by
  exact
    Complex.finiteAbelPlana_log_puncturedRectangle_boundaryAccounting
      hw N T hT hρ hρR

/-- Positive radii satisfying the punctured-rectangle geometric bound occur
eventually at `𝓝[>] 0`. -/
theorem Complex.eventually_pos_lt_finiteAbelPlanaLogPuncturedRectangleRadiusBound
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    {T : ℝ}
    (hT : 0 < T) :
    ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
      0 < ρ ∧
        ρ < Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T := by
  have hR :
      0 < Complex.finiteAbelPlanaLogPuncturedRectangleRadiusBound w N T :=
    Complex.finiteAbelPlana_log_puncturedRectangleRadiusBound_pos
      hw N hT
  exact
    (Ioo_mem_nhdsWithin_Ioi ⟨by linarith, hR⟩).mono
      (fun ρ hρ => ⟨hρ.1, hρ.2⟩)

/-- The punctured-rectangle Cauchy-Goursat identity before taking residues.

For sufficiently small positive `ρ`, remove the radius-`ρ` disks around the
integer poles `0, ..., N+1`.  The boundary of the excised rectangle is the
outer rectangle boundary minus the normalized small circles, and its limit is
zero. -/
theorem Complex.finiteAbelPlana_log_puncturedRectangleCauchyGoursat_pvSmallCircles
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
          Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ℂ)) := by
  have hevent :
      ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
        Complex.finiteAbelPlanaLogFiniteHeightRectangleSideExpressionPVNormalized N w T ρ -
            Complex.finiteAbelPlanaLogPVDeletedBoundaryIntegralContribution N w ρ =
          0 := by
      filter_upwards
        [Complex.eventually_pos_lt_finiteAbelPlanaLogPuncturedRectangleRadiusBound
          hw N hT] with ρ hρ
      exact
        Complex.finiteAbelPlana_log_puncturedRectangleBoundary_eq_zero_of_pos_lt_radiusBound
          hw N T hT hρ.1 hρ.2
  exact tendsto_const_nhds.congr' hevent.symm

/-- The normalized small-circle integrals converge to the already-owned local
integer residues, summed over the finite rectangle poles. -/
theorem Complex.finiteAbelPlana_log_normalizedSmallCircleIntegralSum_tendsto_residueContribution
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegralSum N w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogSmallCircleIntegerResidueContribution N w)) := by
  have hlocal :
      ∀ n ∈ Finset.range (N + 2),
        Tendsto
          (fun ρ : ℝ =>
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n : ℂ) ρ)
          (𝓝[>] (0 : ℝ))
          (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n)) :=
    fun n _hn =>
      Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_tendsto_residue
        hw n
  simpa [Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegralSum,
    Complex.finiteAbelPlanaLogSmallCircleIntegerResidueContribution] using
    tendsto_finset_sum (Finset.range (N + 2)) hlocal

/-- Principal-value small-circle integrals converge to the principal-value
integer residue contribution: half endpoint residues plus full interior
residues. -/
theorem Complex.finiteAbelPlana_log_pvSmallCircleIntegralContribution_tendsto_pvResidues
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogPVSmallCircleIntegralContribution N w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  have hleft :
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w 0 ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w 0)) :=
    Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_tendsto_residue
      hw 0
  have hright :
      Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (N + 1 : ℂ) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w (N + 1))) :=
    Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_tendsto_residue
      hw (N + 1)
  have hinterior :
      Tendsto
        (fun ρ : ℝ =>
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w)) := by
    have hlocal :
        ∀ n ∈ Finset.range N,
          Tendsto
            (fun ρ : ℝ =>
              Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n + 1 : ℂ) ρ)
            (𝓝[>] (0 : ℝ))
            (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w (n + 1))) :=
      fun n _hn =>
        Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_tendsto_residue
          hw (n + 1)
    simpa [Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution] using
      tendsto_finset_sum (Finset.range N) hlocal
  have hendpoints :
      Tendsto
        (fun ρ : ℝ =>
          (Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w 0 ρ +
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (N + 1 : ℂ) ρ) / 2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w)) := by
    have hsum := hleft.add hright
    have hhalf :
        Tendsto
          (fun ρ : ℝ =>
            (Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w 0 ρ +
              Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (N + 1 : ℂ) ρ) / 2)
          (𝓝[>] (0 : ℝ))
          (𝓝 ((Complex.finiteAbelPlanaLogIntegerResidue w 0 +
            Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2)) :=
      hsum.div_const 2
    simpa [Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution] using hhalf
  have htotal := hendpoints.add hinterior
  simpa [Complex.finiteAbelPlanaLogPVSmallCircleIntegralContribution,
    Complex.finiteAbelPlanaLogPVIntegerResidueContribution] using htotal

end

end LFunctions
end Boundary
