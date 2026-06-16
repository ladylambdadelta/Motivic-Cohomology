import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaVerticalStrips

/-!
# Rectangular collar geometry for finite-height Abel-Plana

This file owns the basic punctured rectangular collar and half-collar geometry
used by the endpoint indentation argument.  The right-semicircle staircase and
endpoint residue-limit layers live downstream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Closed rectangular collar with one round puncture removed.

This is the owner-level geometric object for the cap/collar pieces omitted by
the safe vertical strips.  Endpoint collars use semicircular variants of the
same pattern; interior collars use this full-disk version directly. -/
def Complex.finiteAbelPlanaLogPuncturedRectangularCollar
    (x₀ x₁ : ℝ)
    (T : ℝ)
    (c : ℂ)
    (ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[x₀, x₁]] ∧ z.im ∈ [[-T, T]]} : Set ℂ) \
    Metric.ball c ρ

/-- Membership in a punctured rectangular collar is coordinatewise rectangle
membership plus avoidance of the deleted disk. -/
theorem Complex.mem_finiteAbelPlanaLogPuncturedRectangularCollar_iff
    {x₀ x₁ T ρ : ℝ}
    {c z : ℂ} :
    z ∈ Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ ↔
      z.re ∈ [[x₀, x₁]] ∧ z.im ∈ [[-T, T]] ∧
        z ∉ Metric.ball c ρ := by
  dsimp [Complex.finiteAbelPlanaLogPuncturedRectangularCollar]
  constructor
  · intro hz
    exact ⟨hz.1.1, hz.1.2, hz.2⟩
  · intro hz
    exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩

/-- Set-normalization lemma for feeding collar geometry into the finite
punctured rectangle.

The two hypotheses are the actual geometric obligations: the closed collar
rectangle lies in the ambient finite rectangle, and points of the punctured
collar avoid every deleted pole disk. -/
theorem Complex.finiteAbelPlanaLogPuncturedRectangularCollar_subset_puncturedRectangle
    {N : ℕ}
    {x₀ x₁ T ρ : ℝ}
    {c : ℂ}
    (hrectangle :
      ({z : ℂ | z.re ∈ [[x₀, x₁]] ∧ z.im ∈ [[-T, T]]} : Set ℂ) ⊆
        Complex.finiteAbelPlanaClosedRectangle N T)
    (havoid :
      ∀ z : ℂ,
        z.re ∈ [[x₀, x₁]] →
          z.im ∈ [[-T, T]] →
            z ∉ Metric.ball c ρ →
              ∀ m ∈ Finset.range (N + 2), z ∉ Metric.ball (m : ℂ) ρ) :
    Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  intro z hz
  have hzdata :
      z.re ∈ [[x₀, x₁]] ∧ z.im ∈ [[-T, T]] ∧
        z ∉ Metric.ball c ρ :=
    Complex.mem_finiteAbelPlanaLogPuncturedRectangularCollar_iff.mp hz
  exact
    Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr
      ⟨hrectangle ⟨hzdata.1, hzdata.2.1⟩,
        havoid z hzdata.1 hzdata.2.1 hzdata.2.2⟩

/-- Continuity of the Abel-Plana rectangle integrand on any punctured
rectangular collar contained in the ambient finite punctured rectangle. -/
theorem Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_puncturedRectangularCollar
    {w : ℂ}
    {N : ℕ}
    {x₀ x₁ T ρ : ℝ}
    {c : ℂ}
    (hcollar :
      Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    ContinuousOn
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ) := by
  exact hcont.mono hcollar

/-- Holomorphy of the Abel-Plana rectangle integrand on any punctured
rectangular collar contained in the ambient finite punctured rectangle. -/
theorem Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_puncturedRectangularCollar
    {w : ℂ}
    {N : ℕ}
    {x₀ x₁ T ρ : ℝ}
    {c : ℂ}
    (hcollar :
      Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ ⊆
        Complex.finiteAbelPlanaPuncturedRectangle N T ρ)
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogPuncturedRectangularCollar x₀ x₁ T c ρ) := by
  exact hdiff.mono hcollar

/-- Generic oriented boundary integral of a rectangular collar with one round
deleted disk.

The convention is the ordinary rectangle boundary minus the counterclockwise
inner circular boundary. -/
noncomputable def Complex.puncturedRectangularCollarBoundaryIntegral
    (f : ℂ → ℂ)
    (x₀ x₁ T : ℝ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  (∫ x : ℝ in x₀..x₁, f ((x : ℂ) - Complex.I * (T : ℂ))) -
    (∫ x : ℝ in x₀..x₁, f ((x : ℂ) + Complex.I * (T : ℂ))) +
      Complex.I * (∫ y : ℝ in (-T)..T, f ((x₁ : ℂ) + Complex.I * (y : ℂ))) -
        Complex.I * (∫ y : ℝ in (-T)..T, f ((x₀ : ℂ) + Complex.I * (y : ℂ))) -
          circleIntegral f c ρ

/-- The right half-rectangle collar outside a deleted disk centered at `c`.

This is the local model for a left endpoint indentation: the safe vertical side
is at `Re z = c.re + a`, while the deleted inner boundary is the right
semicircle of radius `ρ` about `c`. -/
def Complex.rightHalfRectangleDeletedDiskDomain
    (c : ℂ)
    (T a ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[c.re, c.re + a]] ∧ z.im ∈ [[c.im - T, c.im + T]]} : Set ℂ) \
    Metric.ball c ρ

/-- The left half-rectangle collar outside a deleted disk centered at `c`.

This is the local model for a right endpoint indentation or the left
semicollar around an interior deleted integer. -/
def Complex.leftHalfRectangleDeletedDiskDomain
    (c : ℂ)
    (T a ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[c.re - a, c.re]] ∧ z.im ∈ [[c.im - T, c.im + T]]} : Set ℂ) \
    Metric.ball c ρ

/-- The actual right half-rectangle collar used by the local indentation
Cauchy theorem.

The ambient `T`-height versions below only supply regularity on a larger
neighborhood.  The curvilinear boundary itself lives at height `ρ`, so this is
the owner domain for the local Cauchy-Goursat theorem. -/
def Complex.rightHalfRectangleDeletedDiskCoreDomain
    (c : ℂ)
    (a ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[c.re, c.re + a]] ∧ z.im ∈ [[c.im - ρ, c.im + ρ]]} : Set ℂ) \
    Metric.ball c ρ

/-- The actual left half-rectangle collar used by the local indentation
Cauchy theorem. -/
def Complex.leftHalfRectangleDeletedDiskCoreDomain
    (c : ℂ)
    (a ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[c.re - a, c.re]] ∧ z.im ∈ [[c.im - ρ, c.im + ρ]]} : Set ℂ) \
    Metric.ball c ρ

/-- Lower quarter of the right tangent-box cap outside the deleted disk. -/
def Complex.rightDeletedDiskLowerTangentBoxCapDomain
    (c : ℂ)
    (ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[c.re, c.re + ρ]] ∧ z.im ∈ [[c.im - ρ, c.im]]} : Set ℂ) \
    Metric.ball c ρ

/-- Upper quarter of the right tangent-box cap outside the deleted disk. -/
def Complex.rightDeletedDiskUpperTangentBoxCapDomain
    (c : ℂ)
    (ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[c.re, c.re + ρ]] ∧ z.im ∈ [[c.im, c.im + ρ]]} : Set ℂ) \
    Metric.ball c ρ

/-- The right semicircle written as a graph over the vertical coordinate. -/
noncomputable def Complex.rightDeletedDiskTangentBoxCircleGraphRe
    (c : ℂ)
    (ρ y : ℝ) : ℝ :=
  c.re + Real.sqrt (ρ ^ 2 - (y - c.im) ^ 2)

/-- The lower tangent-box cap as the closed graph region to the right of the
deleted circle.  This is the domain used by the polygonal-exhaustion proof of
the lower quarter-cap Cauchy theorem. -/
def Complex.rightDeletedDiskLowerTangentBoxGraphDomain
    (c : ℂ)
    (ρ : ℝ) : Set ℂ :=
  {z : ℂ |
    z.im ∈ [[c.im - ρ, c.im]] ∧
      z.re ∈ [[Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im,
        c.re + ρ]]}

/-- The upper tangent-box cap as the closed graph region to the right of the
deleted circle.  This is the domain used by the polygonal-exhaustion proof of
the upper quarter-cap Cauchy theorem. -/
def Complex.rightDeletedDiskUpperTangentBoxGraphDomain
    (c : ℂ)
    (ρ : ℝ) : Set ℂ :=
  {z : ℂ |
    z.im ∈ [[c.im, c.im + ρ]] ∧
      z.re ∈ [[Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im,
        c.re + ρ]]}

/-- Real coordinate form of the right circular graph inside a tangent box.

If `0 ≤ x ≤ ρ` and `|y| ≤ ρ`, then lying outside the open disk of radius `ρ`
is equivalent to lying to the right of the graph
`x = sqrt (ρ² - y²)`. -/
theorem Real.tangentBox_outside_circle_iff_graph_right
    {x y ρ : ℝ}
    (hρ : 0 < ρ)
    (hx : x ∈ [[0, ρ]])
    (hy : y ∈ [[-ρ, ρ]]) :
    ρ ≤ Real.sqrt (x ^ 2 + y ^ 2) ↔
      Real.sqrt (ρ ^ 2 - y ^ 2) ≤ x := by
  have hx_bounds : 0 ≤ x ∧ x ≤ ρ := by
    simpa [Set.uIcc_of_le hρ.le] using hx
  have hy_bounds : -ρ ≤ y ∧ y ≤ ρ := by
    simpa [Set.uIcc_of_le (by linarith [hρ.le] : -ρ ≤ ρ)] using hy
  have hx_nonneg : 0 ≤ x := hx_bounds.1
  have hsum_nonneg : 0 ≤ x ^ 2 + y ^ 2 := by
    exact add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hrad_nonneg : 0 ≤ ρ ^ 2 - y ^ 2 := by
    have hy_abs : |y| ≤ ρ := by
      exact abs_le.mpr ⟨hy_bounds.1, hy_bounds.2⟩
    have hy_sq : y ^ 2 ≤ ρ ^ 2 := by
      simpa [sq_abs] using sq_le_sq.mpr hy_abs
    exact sub_nonneg.mpr hy_sq
  constructor
  · intro hcircle
    have hsquare :
        ρ ^ 2 ≤ x ^ 2 + y ^ 2 := by
      have hmul :
          ρ * ρ ≤
            Real.sqrt (x ^ 2 + y ^ 2) *
              Real.sqrt (x ^ 2 + y ^ 2) :=
        mul_self_le_mul_self hρ.le hcircle
      simpa [sq, Real.mul_self_sqrt hsum_nonneg] using hmul
    exact
      (Real.sqrt_le_iff).mpr
        ⟨hx_nonneg, by nlinarith⟩
  · intro hgraph
    have hgraph_sq : ρ ^ 2 - y ^ 2 ≤ x ^ 2 :=
      (Real.sqrt_le_iff.mp hgraph).2
    have hsquare : ρ ^ 2 ≤ x ^ 2 + y ^ 2 := by
      nlinarith
    exact
      (Real.le_sqrt hρ.le hsum_nonneg).mpr hsquare

/-- Lower half specialization of the tangent-box circle graph criterion. -/
theorem Real.lowerTangentBox_outside_circle_iff_graph_right
    {x y ρ : ℝ}
    (hρ : 0 < ρ)
    (hx : x ∈ [[0, ρ]])
    (hy : y ∈ [[-ρ, 0]]) :
    ρ ≤ Real.sqrt (x ^ 2 + y ^ 2) ↔
      Real.sqrt (ρ ^ 2 - y ^ 2) ≤ x := by
  have hy_full : y ∈ [[-ρ, ρ]] := by
    have hy_bounds : -ρ ≤ y ∧ y ≤ 0 := by
      simpa [Set.uIcc_of_le (by linarith [hρ.le] : -ρ ≤ (0 : ℝ))] using hy
    have hleft : -ρ ≤ y := hy_bounds.1
    have hright : y ≤ ρ := by linarith [hy_bounds.2, hρ.le]
    simpa [Set.uIcc_of_le (by linarith [hρ.le] : -ρ ≤ ρ)] using
      And.intro hleft hright
  exact Real.tangentBox_outside_circle_iff_graph_right hρ hx hy_full

/-- Upper half specialization of the tangent-box circle graph criterion. -/
theorem Real.upperTangentBox_outside_circle_iff_graph_right
    {x y ρ : ℝ}
    (hρ : 0 < ρ)
    (hx : x ∈ [[0, ρ]])
    (hy : y ∈ [[0, ρ]]) :
    ρ ≤ Real.sqrt (x ^ 2 + y ^ 2) ↔
      Real.sqrt (ρ ^ 2 - y ^ 2) ≤ x := by
  have hy_full : y ∈ [[-ρ, ρ]] := by
    have hy_bounds : 0 ≤ y ∧ y ≤ ρ := by
      simpa [Set.uIcc_of_le hρ.le] using hy
    have hleft : -ρ ≤ y := by linarith [hy_bounds.1, hρ.le]
    have hright : y ≤ ρ := hy_bounds.2
    simpa [Set.uIcc_of_le (by linarith [hρ.le] : -ρ ≤ ρ)] using
      And.intro hleft hright
  exact Real.tangentBox_outside_circle_iff_graph_right hρ hx hy_full

/-- The right core collar is the `T = ρ` specialization of the taller ambient
right collar. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreDomain_eq_heightDomain
    (c : ℂ)
    (a ρ : ℝ) :
    Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ =
      Complex.rightHalfRectangleDeletedDiskDomain c ρ a ρ := by
  rfl

/-- The left core collar is the `T = ρ` specialization of the taller ambient
left collar. -/
theorem Complex.leftHalfRectangleDeletedDiskCoreDomain_eq_heightDomain
    (c : ℂ)
    (a ρ : ℝ) :
    Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ =
      Complex.leftHalfRectangleDeletedDiskDomain c ρ a ρ := by
  rfl

/-- The finite right collar core is compact. -/
theorem Complex.isCompact_rightHalfRectangleDeletedDiskCoreDomain_self
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    IsCompact (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
  have hre_order : c.re ≤ c.re + ρ := by linarith [hρ.le]
  have him_order : c.im - ρ ≤ c.im + ρ := by linarith [hρ.le]
  have hrect_closed :
      IsClosed
        ({z : ℂ |
          z.re ∈ [[c.re, c.re + ρ]] ∧
            z.im ∈ [[c.im - ρ, c.im + ρ]]} : Set ℂ) := by
    have hre_closed :
        IsClosed {z : ℂ | z.re ∈ Set.Icc c.re (c.re + ρ)} :=
      isClosed_Icc.preimage Complex.continuous_re
    have him_closed :
        IsClosed {z : ℂ | z.im ∈ Set.Icc (c.im - ρ) (c.im + ρ)} :=
      isClosed_Icc.preimage Complex.continuous_im
    simpa [Set.uIcc_of_le hre_order, Set.uIcc_of_le him_order] using
      hre_closed.inter him_closed
  have hclosed :
      IsClosed (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    dsimp [Complex.rightHalfRectangleDeletedDiskCoreDomain]
    simpa [Set.diff_eq] using hrect_closed.inter isOpen_ball.isClosed_compl
  have hbounded :
      Bornology.IsBounded
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    refine (Metric.isBounded_iff_subset_closedBall c).2 ⟨2 * ρ, ?_⟩
    intro z hz
    have hrect :
        z.re ∈ [[c.re, c.re + ρ]] ∧
          z.im ∈ [[c.im - ρ, c.im + ρ]] := hz.1
    have hre_pair : c.re ≤ z.re ∧ z.re ≤ c.re + ρ := by
      simpa [Set.uIcc_of_le hre_order] using hrect.1
    have him_pair : c.im - ρ ≤ z.im ∧ z.im ≤ c.im + ρ := by
      simpa [Set.uIcc_of_le him_order] using hrect.2
    have hre_abs : |c.re - z.re| ≤ ρ := by
      rw [abs_sub_comm]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have him_abs : |c.im - z.im| ≤ ρ := by
      rw [abs_sub_comm]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hre_sq : (c.re - z.re) ^ 2 ≤ ρ ^ 2 :=
      sq_le_sq.mpr hre_abs
    have him_sq : (c.im - z.im) ^ 2 ≤ ρ ^ 2 :=
      sq_le_sq.mpr him_abs
    have hrad_le :
        (c.re - z.re) ^ 2 + (c.im - z.im) ^ 2 ≤ (2 * ρ) ^ 2 := by
      nlinarith
    have hdist :
        dist c z ≤ Real.sqrt ((2 * ρ) ^ 2) := by
      rw [Complex.dist_eq_re_im]
      exact Real.sqrt_le_sqrt hrad_le
    have hsqrt : Real.sqrt ((2 * ρ) ^ 2) = 2 * ρ :=
      Real.sqrt_sq (mul_nonneg (by norm_num) hρ.le)
    exact mem_closedBall'.mpr (by simpa [hsqrt] using hdist)
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbounded

/-- Continuity on the finite right collar core is uniformly continuous there. -/
theorem Complex.uniformContinuousOn_rightHalfRectangleDeletedDiskCoreDomain_self
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    UniformContinuousOn f
      (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) :=
  (Complex.isCompact_rightHalfRectangleDeletedDiskCoreDomain_self c hρ).
    uniformContinuousOn_of_continuous hcont

/-- Oriented boundary integral of the right half-rectangle core collar outside
the deleted disk.

This is `lower - upper + right vertical - inner right semicircle`, written in
the interval-integral convention already used throughout the Abel-Plana file. -/
noncomputable def Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) : ℂ :=
  (∫ x : ℝ in c.re..(c.re + a),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
      -(∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
        Complex.I *
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
            f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Ordinary rectangular tail of the right deleted half-rectangle core.

This is the straight rectangular piece between the vertical line tangent to the
deleted disk and the safe vertical side at `c.re + a`. -/
noncomputable def Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) : ℂ :=
  (∫ x : ℝ in (c.re + ρ)..(c.re + a),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
    (∫ x : ℝ in (c.re + ρ)..(c.re + a),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
      Complex.I *
        (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
          f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        Complex.I *
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
            f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))

/-- The tangent-width semicircular core of the right deleted half-rectangle.

This is the only genuinely curvilinear local object left after removing the
ordinary rectangular tail. -/
noncomputable def Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c ρ ρ

/-- Lower quarter-cap boundary of the right tangent-box collar.

The boundary is the lower tangent chord, the lower half of the vertical tangent
chord, and the lower circular indentation arc with deleted-boundary
orientation. -/
noncomputable def Complex.rightDeletedDiskLowerTangentBoxCapBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  (∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
    Complex.I *
      (∫ y : ℝ in (c.im - ρ)..c.im,
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      ∫ θ : ℝ in (-(Real.pi / 2))..0,
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Upper quarter-cap boundary of the right tangent-box collar.

The boundary is the upper half of the vertical tangent chord, the upper tangent
chord with opposite orientation, and the upper circular indentation arc with
deleted-boundary orientation. -/
noncomputable def Complex.rightDeletedDiskUpperTangentBoxCapBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  -(∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
    Complex.I *
      (∫ y : ℝ in c.im..(c.im + ρ),
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      ∫ θ : ℝ in 0..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Complex line integral over the straight segment from `z₀` to `z₁`. -/
noncomputable def Complex.lineSegmentIntegral
    (f : ℂ → ℂ)
    (z₀ z₁ : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..1,
    f (((1 - t : ℝ) : ℂ) * z₀ + ((t : ℝ) : ℂ) * z₁) * (z₁ - z₀)

/-- Uniform partition point on `[a,b]`, using `m + 1` subintervals. -/
noncomputable def Real.uniformPartitionPoint
    (a b : ℝ)
    (m k : ℕ) : ℝ :=
  a + ((k : ℝ) / (m + 1 : ℝ)) * (b - a)

/-- Polygonal line integral along a parametrized curve sampled on the uniform
partition of `[a,b]`. -/
noncomputable def Complex.curveUniformPolygonalLineIntegral
    (f : ℂ → ℂ)
    (γ : ℝ → ℂ)
    (a b : ℝ)
    (m : ℕ) : ℂ :=
  ∑ k in Finset.range (m + 1),
    Complex.lineSegmentIntegral f
      (γ (Real.uniformPartitionPoint a b m k))
      (γ (Real.uniformPartitionPoint a b m (k + 1)))

/-- Lower circular-arc sample angle for the `m`th polygonal approximation. -/
noncomputable def Complex.lowerTangentBoxArcSampleAngle
    (m k : ℕ) : ℝ :=
  -(Real.pi / 2) + ((k : ℝ) / (m + 1 : ℝ)) * (Real.pi / 2)

/-- Upper circular-arc sample angle for the `m`th polygonal approximation. -/
noncomputable def Complex.upperTangentBoxArcSampleAngle
    (m k : ℕ) : ℝ :=
  ((k : ℝ) / (m + 1 : ℝ)) * (Real.pi / 2)

/-- Lower circular-arc sample point for the `m`th polygonal approximation. -/
noncomputable def Complex.lowerTangentBoxArcSamplePoint
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  c + (ρ : ℂ) *
    Complex.exp (Complex.I *
      ((Complex.lowerTangentBoxArcSampleAngle m k : ℝ) : ℂ))

/-- Upper circular-arc sample point for the `m`th polygonal approximation. -/
noncomputable def Complex.upperTangentBoxArcSamplePoint
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  c + (ρ : ℂ) *
    Complex.exp (Complex.I *
      ((Complex.upperTangentBoxArcSampleAngle m k : ℝ) : ℂ))

/-- The true lower circular arc integral appearing in the lower tangent-box
boundary. -/
noncomputable def Complex.lowerTangentBoxCircularArcIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  ∫ θ : ℝ in (-(Real.pi / 2))..0,
    f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- The true upper circular arc integral appearing in the upper tangent-box
boundary. -/
noncomputable def Complex.upperTangentBoxCircularArcIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  ∫ θ : ℝ in 0..(Real.pi / 2),
    f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Polygonal chord-chain approximation to the lower circular arc. -/
noncomputable def Complex.lowerTangentBoxPolygonalArcIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  ∑ k in Finset.range (m + 1),
    Complex.lineSegmentIntegral f
      (Complex.lowerTangentBoxArcSamplePoint c ρ m k)
      (Complex.lowerTangentBoxArcSamplePoint c ρ m (k + 1))

/-- Polygonal chord-chain approximation to the upper circular arc. -/
noncomputable def Complex.upperTangentBoxPolygonalArcIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  ∑ k in Finset.range (m + 1),
    Complex.lineSegmentIntegral f
      (Complex.upperTangentBoxArcSamplePoint c ρ m k)
      (Complex.upperTangentBoxArcSamplePoint c ρ m (k + 1))

/-- Polygonal approximation to the lower tangent-box cap boundary. -/
noncomputable def Complex.rightDeletedDiskLowerTangentBoxPolygonalBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  (∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
    Complex.I *
      (∫ y : ℝ in (c.im - ρ)..c.im,
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      Complex.lowerTangentBoxPolygonalArcIntegral f c ρ m

/-- Polygonal approximation to the upper tangent-box cap boundary. -/
noncomputable def Complex.rightDeletedDiskUpperTangentBoxPolygonalBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  -(∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
    Complex.I *
      (∫ y : ℝ in c.im..(c.im + ρ),
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      Complex.upperTangentBoxPolygonalArcIntegral f c ρ m

/-- Oriented boundary integral of the left half-rectangle core collar outside
the deleted disk. -/
noncomputable def Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) : ℂ :=
  (∫ x : ℝ in (c.re - a)..c.re,
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
      -(∫ x : ℝ in (c.re - a)..c.re,
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
        Complex.I *
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
            f (((c.re - a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
      ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Half-turn through the center `c`.  This is the holomorphic rotation that
identifies the left and right indentation collars. -/
noncomputable def Complex.halfTurnAbout
    (c z : ℂ) : ℂ :=
  2 * c - z

/-- Pullback of a function by the half-turn through `c`. -/
noncomputable def Complex.halfTurnPullback
    (c : ℂ)
    (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z : ℂ => f (Complex.halfTurnAbout c z)

/-- The half-turn carries the right core collar into the left core collar.

This is the geometry behind reducing the left indentation Cauchy theorem to
the right one. -/
theorem Complex.halfTurnAbout_mem_leftCore_of_mem_rightCore
    (c z : ℂ)
    (a ρ : ℝ)
    (ha : 0 ≤ a)
    (hρnonneg : 0 ≤ ρ)
    (hz : z ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) :
    Complex.halfTurnAbout c z ∈
      Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ := by
  rcases hz with ⟨hbox, hnot_ball⟩
  rcases hbox with ⟨hre, him⟩
  have hre_bounds :
      c.re ≤ z.re ∧ z.re ≤ c.re + a := by
    simpa [Set.uIcc_of_le (by linarith : c.re ≤ c.re + a)] using hre
  have him_bounds :
      c.im - ρ ≤ z.im ∧ z.im ≤ c.im + ρ := by
    simpa [Set.uIcc_of_le (by linarith : c.im - ρ ≤ c.im + ρ)] using him
  have hturn_re :
      (Complex.halfTurnAbout c z).re = 2 * c.re - z.re := by
    simp [Complex.halfTurnAbout, sub_re, mul_re, two_mul]
  have hturn_im :
      (Complex.halfTurnAbout c z).im = 2 * c.im - z.im := by
    simp [Complex.halfTurnAbout, sub_im, mul_im, two_mul]
  have hleft_re :
      (Complex.halfTurnAbout c z).re ∈ [[c.re - a, c.re]] := by
    rw [hturn_re]
    have horder : c.re - a ≤ c.re := by linarith
    have hlow : c.re - a ≤ 2 * c.re - z.re := by linarith
    have hhigh : 2 * c.re - z.re ≤ c.re := by linarith
    simpa [Set.uIcc_of_le horder] using And.intro hlow hhigh
  have hleft_im :
      (Complex.halfTurnAbout c z).im ∈ [[c.im - ρ, c.im + ρ]] := by
    rw [hturn_im]
    have horder : c.im - ρ ≤ c.im + ρ := by linarith
    have hlow : c.im - ρ ≤ 2 * c.im - z.im := by linarith
    have hhigh : 2 * c.im - z.im ≤ c.im + ρ := by linarith
    simpa [Set.uIcc_of_le horder] using And.intro hlow hhigh
  have hnot_left :
      Complex.halfTurnAbout c z ∉ Metric.ball c ρ := by
    intro hball
    apply hnot_ball
    have hdist :
        dist z c = dist (Complex.halfTurnAbout c z) c := by
      simp [Complex.halfTurnAbout, dist_eq_norm, norm_sub_rev, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc, two_mul]
    rw [Metric.mem_ball] at hball ⊢
    rwa [hdist]
  exact ⟨⟨hleft_re, hleft_im⟩, hnot_left⟩

/-- Pulling back by the half-turn transports continuity from the left core
collar to the right core collar. -/
theorem Complex.continuousOn_halfTurnPullback_rightCore_of_leftCore
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ)
    (ha : 0 ≤ a)
    (hρnonneg : 0 ≤ ρ)
    (hcont :
      ContinuousOn f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    ContinuousOn (Complex.halfTurnPullback c f)
      (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
  have hmap :
      MapsTo (Complex.halfTurnAbout c)
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ)
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    intro z hz
    exact
      Complex.halfTurnAbout_mem_leftCore_of_mem_rightCore c z a ρ ha hρnonneg hz
  have hturn_cont :
      ContinuousOn (Complex.halfTurnAbout c)
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    simpa [Complex.halfTurnAbout] using
      (continuous_const.sub continuous_id).continuousOn
  exact
    hcont.comp_continuousOn hturn_cont hmap

/-- Pulling back by the half-turn transports holomorphy from the left core
collar to the right core collar. -/
theorem Complex.differentiableOn_halfTurnPullback_rightCore_of_leftCore
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ)
    (ha : 0 ≤ a)
    (hρnonneg : 0 ≤ ρ)
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    DifferentiableOn ℂ (Complex.halfTurnPullback c f)
      (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
  intro z hz
  have hmem :
      Complex.halfTurnAbout c z ∈
        Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ :=
    Complex.halfTurnAbout_mem_leftCore_of_mem_rightCore c z a ρ ha hρnonneg hz
  have hturn :
      DifferentiableAt ℂ (Complex.halfTurnAbout c) z := by
    simpa [Complex.halfTurnAbout] using
      ((differentiableAt_const (2 * c)).sub differentiableAt_id)
  exact (hdiff (Complex.halfTurnAbout c z) hmem).comp z hturn

/-- The lower horizontal side of the left core collar is the upper horizontal
side of the right core collar after half-turn pullback. -/
theorem Complex.leftHalfRectangleDeletedDiskCore_lower_eq_halfTurn_right_upper
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) :
    (∫ x : ℝ in (c.re - a)..c.re,
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
      ∫ x : ℝ in c.re..(c.re + a),
        (Complex.halfTurnPullback c f)
          (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
  let F : ℝ → ℂ := fun x : ℝ =>
    f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))
  have hsubst :
      (∫ x : ℝ in c.re..(c.re + a), F (2 * c.re - x)) =
        ∫ x : ℝ in (2 * c.re - (c.re + a))..(2 * c.re - c.re), F x := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := F) (a := c.re) (b := c.re + a) (d := 2 * c.re))
  have hpoint :
      (fun x : ℝ =>
        (Complex.halfTurnPullback c f)
          (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
        fun x : ℝ => F (2 * c.re - x) := by
    funext x
    simp [F, Complex.halfTurnPullback, Complex.halfTurnAbout, sub_re, sub_im,
      mul_re, mul_im, two_mul, add_comm, add_left_comm, add_assoc,
      sub_eq_add_neg]
  rw [hpoint]
  rw [hsubst]
  simp [F, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The upper horizontal side of the left core collar is the lower horizontal
side of the right core collar after half-turn pullback. -/
theorem Complex.leftHalfRectangleDeletedDiskCore_upper_eq_halfTurn_right_lower
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) :
    (∫ x : ℝ in (c.re - a)..c.re,
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
      ∫ x : ℝ in c.re..(c.re + a),
        (Complex.halfTurnPullback c f)
          (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
  let F : ℝ → ℂ := fun x : ℝ =>
    f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))
  have hsubst :
      (∫ x : ℝ in c.re..(c.re + a), F (2 * c.re - x)) =
        ∫ x : ℝ in (2 * c.re - (c.re + a))..(2 * c.re - c.re), F x := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := F) (a := c.re) (b := c.re + a) (d := 2 * c.re))
  have hpoint :
      (fun x : ℝ =>
        (Complex.halfTurnPullback c f)
          (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
        fun x : ℝ => F (2 * c.re - x) := by
    funext x
    simp [F, Complex.halfTurnPullback, Complex.halfTurnAbout, sub_re, sub_im,
      mul_re, mul_im, two_mul, add_comm, add_left_comm, add_assoc,
      sub_eq_add_neg]
  rw [hpoint]
  rw [hsubst]
  simp [F, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The safe vertical side of the left core collar is the safe vertical side of
the right core collar after half-turn pullback. -/
theorem Complex.leftHalfRectangleDeletedDiskCore_vertical_eq_halfTurn_right_vertical
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) :
    (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
      f (((c.re - a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
      ∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        (Complex.halfTurnPullback c f)
          (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
  let F : ℝ → ℂ := fun y : ℝ =>
    f (((c.re - a : ℝ) : ℂ) + Complex.I * (y : ℂ))
  have hsubst :
      (∫ y : ℝ in (c.im - ρ)..(c.im + ρ), F (2 * c.im - y)) =
        ∫ y : ℝ in (2 * c.im - (c.im + ρ))..(2 * c.im - (c.im - ρ)), F y := by
    simpa using
      (intervalIntegral.integral_comp_sub_left
        (f := F) (a := c.im - ρ) (b := c.im + ρ) (d := 2 * c.im))
  have hpoint :
      (fun y : ℝ =>
        (Complex.halfTurnPullback c f)
          (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        fun y : ℝ => F (2 * c.im - y) := by
    funext y
    simp [F, Complex.halfTurnPullback, Complex.halfTurnAbout, sub_re, sub_im,
      mul_re, mul_im, two_mul, add_comm, add_left_comm, add_assoc,
      sub_eq_add_neg]
  rw [hpoint]
  rw [hsubst]
  simp [F, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- The left semicircle is the negative of the right semicircle after half-turn
pullback.

The minus sign is the tangent-vector contribution of the half-turn. -/
theorem Complex.leftHalfRectangleDeletedDiskCore_semicircle_eq_neg_halfTurn_right_semicircle
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) :
    (∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
      f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      -∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        (Complex.halfTurnPullback c f)
          (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  let G : ℝ → ℂ := fun θ : ℝ =>
    f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  let H : ℝ → ℂ := fun θ : ℝ =>
    (Complex.halfTurnPullback c f)
      (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hpoint : ∀ θ : ℝ, H θ = -G (θ + Real.pi) := by
    intro θ
    have hexp :
        Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) =
          -Complex.exp (Complex.I * (θ : ℂ)) := by
      have hsplit :
          Complex.I * (((θ + Real.pi : ℝ) : ℂ)) =
            Complex.I * (θ : ℂ) + Real.pi * Complex.I := by
        ring
      rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    have hturn :
        Complex.halfTurnAbout c
            (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
          c + (ρ : ℂ) *
            Complex.exp (Complex.I * (((θ + Real.pi : ℝ) : ℂ))) := by
      rw [hexp]
      ring_nf [Complex.halfTurnAbout]
    dsimp [H, G, Complex.halfTurnPullback]
    rw [hturn, hexp]
    ring
  have hsubst :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), G (θ + Real.pi)) =
        ∫ θ : ℝ in (-(Real.pi / 2) + Real.pi)..(Real.pi / 2 + Real.pi), G θ := by
    simpa using
      (intervalIntegral.integral_comp_add_right
        (f := G) (a := -(Real.pi / 2)) (b := Real.pi / 2) Real.pi)
  have hH :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), H θ) =
        -∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2), G θ := by
    calc
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), H θ) =
          ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), -G (θ + Real.pi) := by
        apply intervalIntegral.integral_congr
        intro θ _hθ
        exact hpoint θ
      _ = -∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), G (θ + Real.pi) := by
        simp
      _ = -∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2), G θ := by
        rw [hsubst]
        ring_nf
  dsimp [G, H] at hH ⊢
  rw [hH]
  ring

/-- The left core boundary integral is the negative of the right core boundary
integral after pullback by the half-turn.

This is pure boundary reparametrization: the half-turn swaps lower and upper
chords, carries the safe left vertical chord to the safe right vertical chord,
and sends the left semicircle to the right semicircle with the corrected
closed-contour orientation.  The global minus records the orientation reversal
of the half-turn on the boundary chain. -/
theorem Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral_eq_neg_halfTurn_right
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ) :
    Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ =
      -Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral
        (Complex.halfTurnPullback c f) c a ρ := by
  have hlower :
      (∫ x : ℝ in (c.re - a)..c.re,
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
        ∫ x : ℝ in c.re..(c.re + a),
          (Complex.halfTurnPullback c f)
            (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) :=
    Complex.leftHalfRectangleDeletedDiskCore_lower_eq_halfTurn_right_upper
      f c a ρ
  have hupper :
      (∫ x : ℝ in (c.re - a)..c.re,
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
        ∫ x : ℝ in c.re..(c.re + a),
          (Complex.halfTurnPullback c f)
            (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) :=
    Complex.leftHalfRectangleDeletedDiskCore_upper_eq_halfTurn_right_lower
      f c a ρ
  have hvertical :
      (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        f (((c.re - a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        ∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
          (Complex.halfTurnPullback c f)
            (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) :=
    Complex.leftHalfRectangleDeletedDiskCore_vertical_eq_halfTurn_right_vertical
      f c a ρ
  have harc :
      (∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        -∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          (Complex.halfTurnPullback c f)
            (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    Complex.leftHalfRectangleDeletedDiskCore_semicircle_eq_neg_halfTurn_right_semicircle
      f c ρ
  dsimp [Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral,
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral]
  rw [hlower, hupper, hvertical, harc]
  ring

/-- Boundary telescoping for the right deleted half-rectangle from primitive
evaluations on its four oriented pieces. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral_eq_zero_of_primitive_evaluations
    (f F : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ)
    (hbottom :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
    (htop :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
    (hvertical :
      Complex.I *
        (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
          f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
    (harc :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) :
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ = 0 := by
  dsimp [Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral]
  rw [hbottom, htop, hvertical, harc]
  ring

/-- Primitive derivative data along the four right-indentation boundary pieces
gives the four primitive endpoint evaluations by the real fundamental theorem
of calculus. -/
theorem Complex.rightHalfRectangleDeletedDiskCore_primitive_evaluations_of_hasDerivAt
    (f F : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ)
    (hbottom_deriv :
      ∀ x ∈ [[c.re, c.re + a]],
        HasDerivAt
          (fun x : ℝ =>
            F (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
          (f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
          x)
    (hbottom_int :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        volume c.re (c.re + a))
    (htop_deriv :
      ∀ x ∈ [[c.re, c.re + a]],
        HasDerivAt
          (fun x : ℝ =>
            F (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
          (f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
          x)
    (htop_int :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        volume c.re (c.re + a))
    (hvertical_deriv :
      ∀ y ∈ [[c.im - ρ, c.im + ρ]],
        HasDerivAt
          (fun y : ℝ =>
            F (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          (Complex.I *
            f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          y)
    (hvertical_int :
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.I *
            f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume (c.im - ρ) (c.im + ρ))
    (harc_deriv :
      ∀ θ ∈ [[-(Real.pi / 2), Real.pi / 2]],
        HasDerivAt
          (fun θ : ℝ =>
            F (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          (f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))))
          θ)
    (harc_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))))
        volume (-(Real.pi / 2)) (Real.pi / 2)) :
    (∫ x : ℝ in c.re..(c.re + a),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
      F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) -
        F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) ∧
    (∫ x : ℝ in c.re..(c.re + a),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
      F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
        F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) ∧
    Complex.I *
      (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
      F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) ∧
    (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
      f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
        F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
  have hbottom_eval :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hbottom_deriv hbottom_int
  have htop_eval :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      htop_deriv htop_int
  have hvertical_eval_integrand :
      (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        Complex.I *
          f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hvertical_deriv hvertical_int
  have hvertical_eval :
      Complex.I *
        (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
          f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
    simpa [intervalIntegral.integral_const_mul] using hvertical_eval_integrand
  have harc_eval :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        F (c + (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) -
          F (c + (ρ : ℂ) * Complex.exp (Complex.I * (((-(Real.pi / 2)) : ℝ) : ℂ))) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      harc_deriv harc_int
  have htop_point :
      c + (ρ : ℂ) * Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) =
        (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
    simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
  have hbottom_point :
      c + (ρ : ℂ) * Complex.exp (Complex.I * (((-(Real.pi / 2)) : ℝ) : ℂ)) =
        (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
    simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
  have harc_eval_named :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) -
          F (((c.re : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
    simpa [htop_point, hbottom_point] using harc_eval
  exact ⟨hbottom_eval, htop_eval, hvertical_eval, harc_eval_named⟩

/-- Rectangle/annulus exhaustion for the right deleted half-rectangle collar.

This is the true local topological input.  The curvilinear half-collar is
obtained as a finite rectangle/annular exhaustion; Cauchy-Goursat kills the
piece boundaries and the internal straight/circular edges cancel, leaving
exactly the named outer boundary integral. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_semicircularCore_add_rectangularTail
    (f : ℂ → ℂ)
    (c : ℂ)
    (a ρ : ℝ)
    (hρa : ρ ≤ a)
    (hbottom₁ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        volume c.re (c.re + ρ))
    (hbottom₂ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        volume (c.re + ρ) (c.re + a))
    (htop₁ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        volume c.re (c.re + ρ))
    (htop₂ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        volume (c.re + ρ) (c.re + a)) :
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ =
      Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral f c ρ +
        Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral f c a ρ := by
  have hbottom_split :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) =
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
          ∫ x : ℝ in (c.re + ρ)..(c.re + a),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) := by
    exact (intervalIntegral.integral_add_adjacent_intervals hbottom₁ hbottom₂).symm
  have htop_split :
      (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) =
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
          ∫ x : ℝ in (c.re + ρ)..(c.re + a),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
    exact (intervalIntegral.integral_add_adjacent_intervals htop₁ htop₂).symm
  dsimp [Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral,
    Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral,
    Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral]
  rw [hbottom_split, htop_split]
  ring

/-- The full right tangent-box cap boundary is the sum of its lower and upper
quarter-cap boundaries.

This is only interval splitting and orientation bookkeeping.  The Cauchy
theorem for the two quarter-caps is proved separately. -/
theorem Complex.rightDeletedDiskTangentBoxCapBoundary_eq_lower_add_upper
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (hvertical_lower :
      IntervalIntegrable
        (fun y : ℝ =>
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume (c.im - ρ) c.im)
    (hvertical_upper :
      IntervalIntegrable
        (fun y : ℝ =>
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume c.im (c.im + ρ))
    (harc_lower :
      IntervalIntegrable
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))))
        volume (-(Real.pi / 2)) 0)
    (harc_upper :
      IntervalIntegrable
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))))
        volume 0 (Real.pi / 2)) :
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c ρ ρ =
      Complex.rightDeletedDiskLowerTangentBoxCapBoundaryIntegral f c ρ +
        Complex.rightDeletedDiskUpperTangentBoxCapBoundaryIntegral f c ρ := by
  have hvertical_split :
      (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        (∫ y : ℝ in (c.im - ρ)..c.im,
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in c.im..(c.im + ρ),
            f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
    exact
      (intervalIntegral.integral_add_adjacent_intervals
        hvertical_lower hvertical_upper).symm
  have harc_split :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) *
            Complex.exp (Complex.I * (θ : ℂ)))) =
        (∫ θ : ℝ in (-(Real.pi / 2))..0,
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ)))) +
          ∫ θ : ℝ in 0..(Real.pi / 2),
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) *
                Complex.exp (Complex.I * (θ : ℂ))) := by
    exact
      (intervalIntegral.integral_add_adjacent_intervals
        harc_lower harc_upper).symm
  dsimp [Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral,
    Complex.rightDeletedDiskLowerTangentBoxCapBoundaryIntegral,
    Complex.rightDeletedDiskUpperTangentBoxCapBoundaryIntegral]
  rw [hvertical_split, harc_split]
  ring

/-- The lower quarter tangent-box cap is contained in the full tangent-box
core. -/
theorem Complex.rightDeletedDiskLowerTangentBoxCapDomain_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    Complex.rightDeletedDiskLowerTangentBoxCapDomain c ρ ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  intro z hz
  rcases hz with ⟨hbox, hnot_ball⟩
  rcases hbox with ⟨hre, him⟩
  have hre_core : z.re ∈ [[c.re, c.re + ρ]] := hre
  have him_lower_bounds :
      c.im - ρ ≤ z.im ∧ z.im ≤ c.im := by
    simpa [Set.uIcc_of_le (by linarith [hρ.le] :
      c.im - ρ ≤ c.im)] using him
  have him_core : z.im ∈ [[c.im - ρ, c.im + ρ]] := by
    have hleft : c.im - ρ ≤ z.im := him_lower_bounds.1
    have hright : z.im ≤ c.im + ρ := by linarith [him_lower_bounds.2, hρ.le]
    simpa [Set.uIcc_of_le (by linarith [hρ.le] :
      c.im - ρ ≤ c.im + ρ)] using And.intro hleft hright
  exact ⟨⟨hre_core, him_core⟩, hnot_ball⟩

/-- The upper quarter tangent-box cap is contained in the full tangent-box
core. -/
theorem Complex.rightDeletedDiskUpperTangentBoxCapDomain_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    Complex.rightDeletedDiskUpperTangentBoxCapDomain c ρ ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  intro z hz
  rcases hz with ⟨hbox, hnot_ball⟩
  rcases hbox with ⟨hre, him⟩
  have hre_core : z.re ∈ [[c.re, c.re + ρ]] := hre
  have him_upper_bounds :
      c.im ≤ z.im ∧ z.im ≤ c.im + ρ := by
    simpa [Set.uIcc_of_le (by linarith [hρ.le] :
      c.im ≤ c.im + ρ)] using him
  have him_core : z.im ∈ [[c.im - ρ, c.im + ρ]] := by
    have hleft : c.im - ρ ≤ z.im := by linarith [him_upper_bounds.1, hρ.le]
    have hright : z.im ≤ c.im + ρ := him_upper_bounds.2
    simpa [Set.uIcc_of_le (by linarith [hρ.le] :
      c.im - ρ ≤ c.im + ρ)] using And.intro hleft hright
  exact ⟨⟨hre_core, him_core⟩, hnot_ball⟩

/-- The lower tangent-box cap is equivalently the lower graph region to the
right of the circular boundary. -/
theorem Complex.rightDeletedDiskLowerTangentBoxCapDomain_eq_graphDomain
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    Complex.rightDeletedDiskLowerTangentBoxCapDomain c ρ =
      Complex.rightDeletedDiskLowerTangentBoxGraphDomain c ρ := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hbox, hnot_ball⟩
    rcases hbox with ⟨hre, him⟩
    have hre_bounds : c.re ≤ z.re ∧ z.re ≤ c.re + ρ := by
      simpa [Set.uIcc_of_le (by linarith [hρ.le] :
        c.re ≤ c.re + ρ)] using hre
    have him_bounds : c.im - ρ ≤ z.im ∧ z.im ≤ c.im := by
      simpa [Set.uIcc_of_le (by linarith [hρ.le] :
        c.im - ρ ≤ c.im)] using him
    have hx : z.re - c.re ∈ [[0, ρ]] := by
      have hleft : 0 ≤ z.re - c.re := by linarith [hre_bounds.1]
      have hright : z.re - c.re ≤ ρ := by linarith [hre_bounds.2]
      simpa [Set.uIcc_of_le hρ.le] using And.intro hleft hright
    have hy : z.im - c.im ∈ [[-ρ, 0]] := by
      have hleft : -ρ ≤ z.im - c.im := by linarith [him_bounds.1]
      have hright : z.im - c.im ≤ 0 := by linarith [him_bounds.2]
      simpa [Set.uIcc_of_le (by linarith [hρ.le] : -ρ ≤ (0 : ℝ))] using
        And.intro hleft hright
    have hdist_ge : ρ ≤ dist z c := by
      exact le_of_not_gt (by simpa [Metric.mem_ball] using hnot_ball)
    have hcircle :
        ρ ≤ Real.sqrt ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) := by
      simpa [Complex.dist_eq_re_im] using hdist_ge
    have hgraph_shift :
        Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re :=
      (Real.lowerTangentBox_outside_circle_iff_graph_right hρ hx hy).mp hcircle
    have him_graph : z.im ∈ [[c.im - ρ, c.im]] := him
    have hre_graph : z.re ∈
        [[Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im,
          c.re + ρ]] := by
      have hleft :
          Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ z.re := by
        dsimp [Complex.rightDeletedDiskTangentBoxCircleGraphRe]
        linarith
      have hright : z.re ≤ c.re + ρ := hre_bounds.2
      simpa [Set.uIcc_of_le (by
        dsimp [Complex.rightDeletedDiskTangentBoxCircleGraphRe]
        linarith [Real.sqrt_nonneg (ρ ^ 2 - (z.im - c.im) ^ 2), hρ.le] :
          Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ c.re + ρ)] using
        And.intro hleft hright
    exact ⟨him_graph, hre_graph⟩
  · intro hz
    rcases hz with ⟨him, hre_graph⟩
    have him_bounds : c.im - ρ ≤ z.im ∧ z.im ≤ c.im := by
      simpa [Set.uIcc_of_le (by linarith [hρ.le] :
        c.im - ρ ≤ c.im)] using him
    have hre_graph_bounds :
        Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ z.re ∧
          z.re ≤ c.re + ρ := by
      simpa [Set.uIcc_of_le (by
        dsimp [Complex.rightDeletedDiskTangentBoxCircleGraphRe]
        linarith [Real.sqrt_nonneg (ρ ^ 2 - (z.im - c.im) ^ 2), hρ.le] :
          Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ c.re + ρ)] using
        hre_graph
    have hre_bounds : c.re ≤ z.re ∧ z.re ≤ c.re + ρ := by
      have hleft : c.re ≤ z.re := by
        dsimp [Complex.rightDeletedDiskTangentBoxCircleGraphRe] at hre_graph_bounds
        linarith [Real.sqrt_nonneg (ρ ^ 2 - (z.im - c.im) ^ 2),
          hre_graph_bounds.1]
      exact ⟨hleft, hre_graph_bounds.2⟩
    have hx : z.re - c.re ∈ [[0, ρ]] := by
      have hleft : 0 ≤ z.re - c.re := by linarith [hre_bounds.1]
      have hright : z.re - c.re ≤ ρ := by linarith [hre_bounds.2]
      simpa [Set.uIcc_of_le hρ.le] using And.intro hleft hright
    have hy : z.im - c.im ∈ [[-ρ, 0]] := by
      have hleft : -ρ ≤ z.im - c.im := by linarith [him_bounds.1]
      have hright : z.im - c.im ≤ 0 := by linarith [him_bounds.2]
      simpa [Set.uIcc_of_le (by linarith [hρ.le] : -ρ ≤ (0 : ℝ))] using
        And.intro hleft hright
    have hgraph_shift :
        Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re := by
      dsimp [Complex.rightDeletedDiskTangentBoxCircleGraphRe] at hre_graph_bounds
      linarith
    have hcircle :
        ρ ≤ Real.sqrt ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) :=
      (Real.lowerTangentBox_outside_circle_iff_graph_right hρ hx hy).mpr
        hgraph_shift
    have hnot_ball : z ∉ Metric.ball c ρ := by
      intro hball
      have hdist_lt : dist z c < ρ := by
        simpa [Metric.mem_ball] using hball
      have hdist_ge : ρ ≤ dist z c := by
        simpa [Complex.dist_eq_re_im] using hcircle
      exact not_lt_of_ge hdist_ge hdist_lt
    have hre_box : z.re ∈ [[c.re, c.re + ρ]] := by
      simpa [Set.uIcc_of_le (by linarith [hρ.le] :
        c.re ≤ c.re + ρ)] using hre_bounds
    exact ⟨⟨hre_box, him⟩, hnot_ball⟩

/-- The upper tangent-box cap is equivalently the upper graph region to the
right of the circular boundary. -/
theorem Complex.rightDeletedDiskUpperTangentBoxCapDomain_eq_graphDomain
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    Complex.rightDeletedDiskUpperTangentBoxCapDomain c ρ =
      Complex.rightDeletedDiskUpperTangentBoxGraphDomain c ρ := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hbox, hnot_ball⟩
    rcases hbox with ⟨hre, him⟩
    have hre_bounds : c.re ≤ z.re ∧ z.re ≤ c.re + ρ := by
      simpa [Set.uIcc_of_le (by linarith [hρ.le] :
        c.re ≤ c.re + ρ)] using hre
    have him_bounds : c.im ≤ z.im ∧ z.im ≤ c.im + ρ := by
      simpa [Set.uIcc_of_le (by linarith [hρ.le] :
        c.im ≤ c.im + ρ)] using him
    have hx : z.re - c.re ∈ [[0, ρ]] := by
      have hleft : 0 ≤ z.re - c.re := by linarith [hre_bounds.1]
      have hright : z.re - c.re ≤ ρ := by linarith [hre_bounds.2]
      simpa [Set.uIcc_of_le hρ.le] using And.intro hleft hright
    have hy : z.im - c.im ∈ [[0, ρ]] := by
      have hleft : 0 ≤ z.im - c.im := by linarith [him_bounds.1]
      have hright : z.im - c.im ≤ ρ := by linarith [him_bounds.2]
      simpa [Set.uIcc_of_le hρ.le] using And.intro hleft hright
    have hdist_ge : ρ ≤ dist z c := by
      exact le_of_not_gt (by simpa [Metric.mem_ball] using hnot_ball)
    have hcircle :
        ρ ≤ Real.sqrt ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) := by
      simpa [Complex.dist_eq_re_im] using hdist_ge
    have hgraph_shift :
        Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re :=
      (Real.upperTangentBox_outside_circle_iff_graph_right hρ hx hy).mp hcircle
    have him_graph : z.im ∈ [[c.im, c.im + ρ]] := him
    have hre_graph : z.re ∈
        [[Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im,
          c.re + ρ]] := by
      have hleft :
          Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ z.re := by
        dsimp [Complex.rightDeletedDiskTangentBoxCircleGraphRe]
        linarith
      have hright : z.re ≤ c.re + ρ := hre_bounds.2
      simpa [Set.uIcc_of_le (by
        dsimp [Complex.rightDeletedDiskTangentBoxCircleGraphRe]
        linarith [Real.sqrt_nonneg (ρ ^ 2 - (z.im - c.im) ^ 2), hρ.le] :
          Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ c.re + ρ)] using
        And.intro hleft hright
    exact ⟨him_graph, hre_graph⟩
  · intro hz
    rcases hz with ⟨him, hre_graph⟩
    have him_bounds : c.im ≤ z.im ∧ z.im ≤ c.im + ρ := by
      simpa [Set.uIcc_of_le (by linarith [hρ.le] :
        c.im ≤ c.im + ρ)] using him
    have hre_graph_bounds :
        Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ z.re ∧
          z.re ≤ c.re + ρ := by
      simpa [Set.uIcc_of_le (by
        dsimp [Complex.rightDeletedDiskTangentBoxCircleGraphRe]
        linarith [Real.sqrt_nonneg (ρ ^ 2 - (z.im - c.im) ^ 2), hρ.le] :
          Complex.rightDeletedDiskTangentBoxCircleGraphRe c ρ z.im ≤ c.re + ρ)] using
        hre_graph
    have hre_bounds : c.re ≤ z.re ∧ z.re ≤ c.re + ρ := by
      have hleft : c.re ≤ z.re := by
        dsimp [Complex.rightDeletedDiskTangentBoxCircleGraphRe] at hre_graph_bounds
        linarith [Real.sqrt_nonneg (ρ ^ 2 - (z.im - c.im) ^ 2),
          hre_graph_bounds.1]
      exact ⟨hleft, hre_graph_bounds.2⟩
    have hx : z.re - c.re ∈ [[0, ρ]] := by
      have hleft : 0 ≤ z.re - c.re := by linarith [hre_bounds.1]
      have hright : z.re - c.re ≤ ρ := by linarith [hre_bounds.2]
      simpa [Set.uIcc_of_le hρ.le] using And.intro hleft hright
    have hy : z.im - c.im ∈ [[0, ρ]] := by
      have hleft : 0 ≤ z.im - c.im := by linarith [him_bounds.1]
      have hright : z.im - c.im ≤ ρ := by linarith [him_bounds.2]
      simpa [Set.uIcc_of_le hρ.le] using And.intro hleft hright
    have hgraph_shift :
        Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re := by
      dsimp [Complex.rightDeletedDiskTangentBoxCircleGraphRe] at hre_graph_bounds
      linarith
    have hcircle :
        ρ ≤ Real.sqrt ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) :=
      (Real.upperTangentBox_outside_circle_iff_graph_right hρ hx hy).mpr
        hgraph_shift
    have hnot_ball : z ∉ Metric.ball c ρ := by
      intro hball
      have hdist_lt : dist z c < ρ := by
        simpa [Metric.mem_ball] using hball
      have hdist_ge : ρ ≤ dist z c := by
        simpa [Complex.dist_eq_re_im] using hcircle
      exact not_lt_of_ge hdist_ge hdist_lt
    have hre_box : z.re ∈ [[c.re, c.re + ρ]] := by
      simpa [Set.uIcc_of_le (by linarith [hρ.le] :
        c.re ≤ c.re + ρ)] using hre_bounds
    exact ⟨⟨hre_box, him⟩, hnot_ball⟩

/-- If a sequence is identically zero and tends to `a`, then `a = 0`. -/
theorem Complex.eq_zero_of_tendsto_identically_zero

end

end LFunctions
end Boundary
