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

/-- Unfolding of the finite normalized small-circle sum. -/
theorem Complex.finiteAbelPlana_log_normalizedSmallCircleIntegralSum_unfold
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegralSum N w ρ =
      ∑ n in Finset.range (N + 2),
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n : ℂ) ρ := by
  rfl

/-- Nat-cast-normalized unfolding of the principal-value small-circle
contribution. -/
theorem Complex.finiteAbelPlana_log_pvSmallCircleIntegralContribution_natCast_unfold
    (N : ℕ)
    (w : ℂ)
    (ρ : ℝ) :
    Complex.finiteAbelPlanaLogPVSmallCircleIntegralContribution N w ρ =
      (Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((0 : ℕ) : ℂ) ρ +
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((N + 1 : ℕ) : ℂ) ρ) / 2 +
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((n + 1 : ℕ) : ℂ) ρ := by
  have hzero_arg :
      (0 : ℂ) = ((0 : ℕ) : ℂ) :=
    (Nat.cast_zero : (((0 : ℕ) : ℂ) = 0)).symm
  exact
    Eq.trans
      (Complex.finiteAbelPlana_log_pvSmallCircleIntegralContribution_unfold
        N w ρ)
      (congrArg
        (fun z : ℂ =>
          (Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w z ρ +
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
              w ((N + 1 : ℕ) : ℂ) ρ) / 2 +
              ∑ n in Finset.range N,
                Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral
                  w ((n + 1 : ℕ) : ℂ) ρ)
        hzero_arg)

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
    Filter.mem_of_superset
      (Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, hR⟩)
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
    Filter.Tendsto
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
    exact
      (Complex.eventually_pos_lt_finiteAbelPlanaLogPuncturedRectangleRadiusBound
        hw N hT).mono
        (fun ρ hρ =>
          Complex.finiteAbelPlana_log_puncturedRectangleBoundary_eq_zero_of_pos_lt_radiusBound
            hw N T hT hρ.1 hρ.2)
  exact tendsto_const_nhds.congr'
    (hevent.mono (fun ρ hρ => hρ.symm))

/-- The normalized small-circle integrals converge to the already-owned local
integer residues, summed over the finite rectangle poles. -/
theorem Complex.finiteAbelPlana_log_normalizedSmallCircleIntegralSum_tendsto_residueContribution
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegralSum N w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogSmallCircleIntegerResidueContribution N w)) := by
  have hlocal :
      ∀ n ∈ Finset.range (N + 2),
        Filter.Tendsto
          (fun ρ : ℝ =>
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n : ℂ) ρ)
          (𝓝[>] (0 : ℝ))
          (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w n)) :=
    fun n _hn =>
      Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_tendsto_residue
        hw n
  have hsum :
      Filter.Tendsto
        (fun ρ : ℝ =>
          ∑ n in Finset.range (N + 2),
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n : ℂ) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (∑ n in Finset.range (N + 2),
            Complex.finiteAbelPlanaLogIntegerResidue w n)) :=
    tendsto_finset_sum (Finset.range (N + 2)) hlocal
  have hsource :
      (fun ρ : ℝ =>
        ∑ n in Finset.range (N + 2),
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w (n : ℂ) ρ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegralSum N w ρ) :=
    Filter.Eventually.of_forall
      (fun ρ =>
        (Complex.finiteAbelPlana_log_normalizedSmallCircleIntegralSum_unfold
          N w ρ).symm)
  have htarget :
      (∑ n in Finset.range (N + 2),
        Complex.finiteAbelPlanaLogIntegerResidue w n) =
      Complex.finiteAbelPlanaLogSmallCircleIntegerResidueContribution N w :=
    (Complex.finiteAbelPlana_log_smallCircleIntegerResidueContribution_unfold
      N w).symm
  exact (htarget ▸ hsum).congr' hsource

/-- The interior principal-value small circles converge to the full interior
integer residue contribution. -/
theorem Complex.finiteAbelPlana_log_pvInteriorSmallCircleIntegral_tendsto_residues
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        ∑ n in Finset.range N,
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((n + 1 : ℕ) : ℂ) ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w)) := by
  have hlocal :
      ∀ n ∈ Finset.range N,
        Filter.Tendsto
          (fun ρ : ℝ =>
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((n + 1 : ℕ) : ℂ) ρ)
          (𝓝[>] (0 : ℝ))
          (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w (n + 1))) :=
    fun n _hn =>
      Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_tendsto_residue
        hw (n + 1)
  have hsum :
      Filter.Tendsto
        (fun ρ : ℝ =>
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((n + 1 : ℕ) : ℂ) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogIntegerResidue w (n + 1))) :=
    tendsto_finset_sum (Finset.range N) hlocal
  have htarget :
      (∑ n in Finset.range N,
        Complex.finiteAbelPlanaLogIntegerResidue w (n + 1)) =
      Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w :=
    (Complex.finiteAbelPlana_log_interiorIntegerResidueContribution_unfold
      N w).symm
  exact htarget ▸ hsum

/-- The endpoint principal-value small circles converge to the raw endpoint
half-residue expression. -/
theorem Complex.finiteAbelPlana_log_pvEndpointSmallCircleIntegral_tendsto_rawResidues
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        (Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((0 : ℕ) : ℂ) ρ +
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((N + 1 : ℕ) : ℂ) ρ) / 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((Complex.finiteAbelPlanaLogIntegerResidue w 0 +
        Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2)) := by
  have hleft :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((0 : ℕ) : ℂ) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w 0)) :=
    Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_tendsto_residue
      hw 0
  have hright :
      Filter.Tendsto
        (fun ρ : ℝ =>
          Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((N + 1 : ℕ) : ℂ) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogIntegerResidue w (N + 1))) :=
    Complex.finiteAbelPlana_log_normalizedSmallCircleIntegral_tendsto_residue
      hw (N + 1)
  have hsum := hleft.add hright
  have hhalf :
      Filter.Tendsto
        (fun ρ : ℝ =>
          (Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((0 : ℕ) : ℂ) ρ +
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((N + 1 : ℕ) : ℂ) ρ) / 2)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((Complex.finiteAbelPlanaLogIntegerResidue w 0 +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2)) :=
    hsum.div_const 2
  exact hhalf

/-- Principal-value small-circle integrals converge to the endpoint-plus-interior
integer residue contribution. -/
theorem Complex.finiteAbelPlana_log_pvSmallCircleIntegralContribution_tendsto_endpoint_add_interior_residues
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogPVSmallCircleIntegralContribution N w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝
        (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w)) := by
  have hinterior :
      Filter.Tendsto
        (fun ρ : ℝ =>
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((n + 1 : ℕ) : ℂ) ρ)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w)) :=
    Complex.finiteAbelPlana_log_pvInteriorSmallCircleIntegral_tendsto_residues
      hw N
  have hendpoints :
      Filter.Tendsto
        (fun ρ : ℝ =>
          (Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((0 : ℕ) : ℂ) ρ +
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((N + 1 : ℕ) : ℂ) ρ) / 2)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((Complex.finiteAbelPlanaLogIntegerResidue w 0 +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2)) :=
    Complex.finiteAbelPlana_log_pvEndpointSmallCircleIntegral_tendsto_rawResidues
      hw N
  have hendpointTarget :
      (Complex.finiteAbelPlanaLogIntegerResidue w 0 +
          Complex.finiteAbelPlanaLogIntegerResidue w (N + 1)) / 2 =
        Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w :=
    (Complex.finiteAbelPlana_log_endpointIntegerResidueContribution_unfold
      N w).symm
  have hendpointsNamed :
      Filter.Tendsto
        (fun ρ : ℝ =>
          (Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((0 : ℕ) : ℂ) ρ +
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((N + 1 : ℕ) : ℂ) ρ) / 2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w)) :=
    hendpointTarget ▸ hendpoints
  have htotal := hendpointsNamed.add hinterior
  have hsource :
      (fun ρ : ℝ =>
        (Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((0 : ℕ) : ℂ) ρ +
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((N + 1 : ℕ) : ℂ) ρ) / 2 +
          ∑ n in Finset.range N,
            Complex.finiteAbelPlanaLogNormalizedSmallCircleIntegral w ((n + 1 : ℕ) : ℂ) ρ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogPVSmallCircleIntegralContribution N w ρ) :=
    Filter.Eventually.of_forall
      (fun ρ =>
        (Complex.finiteAbelPlana_log_pvSmallCircleIntegralContribution_natCast_unfold
          N w ρ).symm)
  exact htotal.congr' hsource

/-- Principal-value small-circle integrals converge to the principal-value
integer residue contribution: half endpoint residues plus full interior
residues. -/
theorem Complex.finiteAbelPlana_log_pvSmallCircleIntegralContribution_tendsto_pvResidues
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Filter.Tendsto
      (fun ρ : ℝ =>
        Complex.finiteAbelPlanaLogPVSmallCircleIntegralContribution N w ρ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w)) := by
  have htarget :
      Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N w +
          Complex.finiteAbelPlanaLogInteriorIntegerResidueContribution N w =
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w :=
    (Complex.finiteAbelPlana_log_pvIntegerResidueContribution_unfold
      N w).symm
  exact
    htarget ▸
      Complex.finiteAbelPlana_log_pvSmallCircleIntegralContribution_tendsto_endpoint_add_interior_residues
        hw N

end

end LFunctions
end Boundary
