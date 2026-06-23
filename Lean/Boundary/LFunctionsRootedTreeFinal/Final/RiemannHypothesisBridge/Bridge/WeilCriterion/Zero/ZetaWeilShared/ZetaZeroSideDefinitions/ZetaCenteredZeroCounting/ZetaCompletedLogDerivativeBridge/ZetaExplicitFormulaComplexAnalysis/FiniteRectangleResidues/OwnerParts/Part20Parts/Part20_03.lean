import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_02

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

/-!
## Part20 03: SortedEndpointsAndOuterIntegrals
-/

theorem explicitFormulaRectangleSortedXEndpoints_mem_outerLeft
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) :
    F.c ∈ explicitFormulaRectangleSortedXEndpoints F T ρ :=
  (explicitFormulaRectangleSortedXEndpoints_mem_iff F T ρ F.c).mpr
    (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_left F T ρ)

/-- The outer right horizontal coordinate is present in the sorted horizontal endpoint
list. -/
theorem explicitFormulaRectangleSortedXEndpoints_mem_outerRight
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) :
    1 - F.c ∈ explicitFormulaRectangleSortedXEndpoints F T ρ :=
  (explicitFormulaRectangleSortedXEndpoints_mem_iff F T ρ (1 - F.c)).mpr
    (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_right F T ρ)

/-- The outer lower vertical coordinate is present in the sorted vertical endpoint list. -/
theorem explicitFormulaRectangleSortedYEndpoints_mem_outerLower
    (T ρ : ℝ) :
    -T ∈ explicitFormulaRectangleSortedYEndpoints T ρ :=
  (explicitFormulaRectangleSortedYEndpoints_mem_iff T ρ (-T)).mpr
    (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_lower T ρ)

/-- The outer upper vertical coordinate is present in the sorted vertical endpoint list. -/
theorem explicitFormulaRectangleSortedYEndpoints_mem_outerUpper
    (T ρ : ℝ) :
    T ∈ explicitFormulaRectangleSortedYEndpoints T ρ :=
  (explicitFormulaRectangleSortedYEndpoints_mem_iff T ρ T).mpr
    (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_upper T ρ)

/-- The raw-hole left horizontal coordinate is present in the sorted horizontal endpoint
list. -/
theorem explicitFormulaRectangleSortedXEndpoints_mem_rawHoleLeft
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re ∈
      explicitFormulaRectangleSortedXEndpoints F T ρ :=
  (explicitFormulaRectangleSortedXEndpoints_mem_iff F T ρ
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re).mpr
    (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_holeLeft
      F T ρ ha)

/-- The raw-hole right horizontal coordinate is present in the sorted horizontal endpoint
list. -/
theorem explicitFormulaRectangleSortedXEndpoints_mem_rawHoleRight
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re ∈
      explicitFormulaRectangleSortedXEndpoints F T ρ :=
  (explicitFormulaRectangleSortedXEndpoints_mem_iff F T ρ
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re).mpr
    (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_holeRight
      F T ρ ha)

/-- The raw-hole lower vertical coordinate is present in the sorted vertical endpoint
list. -/
theorem explicitFormulaRectangleSortedYEndpoints_mem_rawHoleBottom
    (T ρ : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im ∈
      explicitFormulaRectangleSortedYEndpoints T ρ :=
  (explicitFormulaRectangleSortedYEndpoints_mem_iff T ρ
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im).mpr
    (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_holeBottom
      T ρ ha)

/-- The raw-hole upper vertical coordinate is present in the sorted vertical endpoint
list. -/
theorem explicitFormulaRectangleSortedYEndpoints_mem_rawHoleTop
    (T ρ : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im ∈
      explicitFormulaRectangleSortedYEndpoints T ρ :=
  (explicitFormulaRectangleSortedYEndpoints_mem_iff T ρ
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im).mpr
    (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_holeTop
      T ρ ha)

/-- The sorted vertical endpoint list is nonempty, because it contains the lower outer
endpoint. -/
theorem explicitFormulaRectangleSortedYEndpoints_length_pos
    (T ρ : ℝ) :
    0 < (explicitFormulaRectangleSortedYEndpoints T ρ).length := by
  exact
    List.length_pos_of_mem
      (explicitFormulaRectangleSortedYEndpoints_mem_outerLower T ρ)

/-- The sorted horizontal endpoint list is nonempty, because it contains the outer right
endpoint. -/
theorem explicitFormulaRectangleSortedXEndpoints_length_pos
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) :
    0 < (explicitFormulaRectangleSortedXEndpoints F T ρ).length := by
  exact
    List.length_pos_of_mem
      (explicitFormulaRectangleSortedXEndpoints_mem_outerRight F T ρ)

/-- The first sorted vertical endpoint is the lower outer endpoint. -/
theorem explicitFormulaRectangleSortedYEndpoints_first_eq_outerLower
    (F : ExplicitFormulaContourFamily) {T ρ : ℝ}
    (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T) :
    (explicitFormulaRectangleSortedYEndpoints T ρ).get
        ⟨0, explicitFormulaRectangleSortedYEndpoints_length_pos T ρ⟩ = -T := by
  let S : Finset ℝ := explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ρ
  have hS_nonempty : S.Nonempty :=
    ⟨-T, explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_lower T ρ⟩
  have hmin_le :
      S.min' hS_nonempty ≤ -T :=
    S.min'_le (-T)
      (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_lower T ρ)
  have hle_min :
      -T ≤ S.min' hS_nonempty :=
    S.le_min' (-T)
      (fun y hy =>
        (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_vertical_Icc_of_closedRadiusControls
          F T ρ hT_nonneg (le_of_lt hρ) hclosed hy).1)
  have hmin_eq :
      S.min' hS_nonempty = -T :=
    le_antisymm hmin_le hle_min
  calc
    (explicitFormulaRectangleSortedYEndpoints T ρ).get
        ⟨0, explicitFormulaRectangleSortedYEndpoints_length_pos T ρ⟩ =
        S.min' hS_nonempty := by
      exact Finset.sorted_zero_eq_min'
    _ = -T := hmin_eq

/-- The last sorted vertical endpoint is the upper outer endpoint. -/
theorem explicitFormulaRectangleSortedYEndpoints_last_eq_outerUpper
    (F : ExplicitFormulaContourFamily) {T ρ : ℝ}
    (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T) :
    (explicitFormulaRectangleSortedYEndpoints T ρ).get
        ⟨(explicitFormulaRectangleSortedYEndpoints T ρ).length - 1,
          Nat.sub_lt
            (explicitFormulaRectangleSortedYEndpoints_length_pos T ρ)
            Nat.zero_lt_one⟩ = T := by
  let S : Finset ℝ := explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ρ
  have hS_nonempty : S.Nonempty :=
    ⟨T, explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_upper T ρ⟩
  have hmax_le :
      S.max' hS_nonempty ≤ T :=
    S.max'_le T
      (fun y hy =>
        (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_vertical_Icc_of_closedRadiusControls
          F T ρ hT_nonneg (le_of_lt hρ) hclosed hy).2)
  have hle_max :
      T ≤ S.max' hS_nonempty :=
    S.le_max' T
      (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_upper T ρ)
  have hmax_eq :
      S.max' hS_nonempty = T :=
    le_antisymm hmax_le hle_max
  calc
    (explicitFormulaRectangleSortedYEndpoints T ρ).get
        ⟨(explicitFormulaRectangleSortedYEndpoints T ρ).length - 1,
          Nat.sub_lt
            (explicitFormulaRectangleSortedYEndpoints_length_pos T ρ)
            Nat.zero_lt_one⟩ =
        S.max' hS_nonempty := by
      exact Finset.sorted_last_eq_max'
    _ = T := hmax_eq

/-- The first sorted horizontal endpoint is the left outer endpoint in increasing
coordinates. -/
theorem explicitFormulaRectangleSortedXEndpoints_first_eq_outerLeft
    (F : ExplicitFormulaContourFamily) {T ρ : ℝ} (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T) :
    (explicitFormulaRectangleSortedXEndpoints F T ρ).get
        ⟨0, explicitFormulaRectangleSortedXEndpoints_length_pos F T ρ⟩ = 1 - F.c := by
  let S : Finset ℝ := explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ρ
  have hS_nonempty : S.Nonempty :=
    ⟨1 - F.c, explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_right F T ρ⟩
  have horder : 1 - F.c ≤ F.c :=
    le_of_lt (lt_trans F.one_sub_c_neg F.c_pos)
  have hspan :
      [[F.c, 1 - F.c]] = Set.Icc (1 - F.c) F.c :=
    Set.uIcc_of_ge horder
  have hmin_le :
      S.min' hS_nonempty ≤ 1 - F.c :=
    S.min'_le (1 - F.c)
      (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_right F T ρ)
  have hle_min :
      1 - F.c ≤ S.min' hS_nonempty :=
    S.le_min' (1 - F.c)
      (fun x hx =>
        have hx_span :
            x ∈ [[F.c, 1 - F.c]] :=
          explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_horizontal_uIcc_of_closedRadiusControls
            F T ρ (le_of_lt hρ) hclosed hx
        have hx_Icc :
            x ∈ Set.Icc (1 - F.c) F.c :=
          Eq.subst
            (motive := fun s : Set ℝ => x ∈ s)
            hspan
            hx_span
        hx_Icc.1)
  have hmin_eq :
      S.min' hS_nonempty = 1 - F.c :=
    le_antisymm hmin_le hle_min
  calc
    (explicitFormulaRectangleSortedXEndpoints F T ρ).get
        ⟨0, explicitFormulaRectangleSortedXEndpoints_length_pos F T ρ⟩ =
        S.min' hS_nonempty := by
      exact Finset.sorted_zero_eq_min'
    _ = 1 - F.c := hmin_eq

/-- The last sorted horizontal endpoint is the right outer endpoint in increasing
coordinates. -/
theorem explicitFormulaRectangleSortedXEndpoints_last_eq_outerRight
    (F : ExplicitFormulaContourFamily) {T ρ : ℝ} (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T) :
    (explicitFormulaRectangleSortedXEndpoints F T ρ).get
        ⟨(explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1,
          Nat.sub_lt
            (explicitFormulaRectangleSortedXEndpoints_length_pos F T ρ)
            Nat.zero_lt_one⟩ = F.c := by
  let S : Finset ℝ := explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ρ
  have hS_nonempty : S.Nonempty :=
    ⟨F.c, explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_left F T ρ⟩
  have horder : 1 - F.c ≤ F.c :=
    le_of_lt (lt_trans F.one_sub_c_neg F.c_pos)
  have hspan :
      [[F.c, 1 - F.c]] = Set.Icc (1 - F.c) F.c :=
    Set.uIcc_of_ge horder
  have hmax_le :
      S.max' hS_nonempty ≤ F.c :=
    S.max'_le F.c
      (fun x hx =>
        have hx_span :
            x ∈ [[F.c, 1 - F.c]] :=
          explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_horizontal_uIcc_of_closedRadiusControls
            F T ρ (le_of_lt hρ) hclosed hx
        have hx_Icc :
            x ∈ Set.Icc (1 - F.c) F.c :=
          Eq.subst
            (motive := fun s : Set ℝ => x ∈ s)
            hspan
            hx_span
        hx_Icc.2)
  have hle_max :
      F.c ≤ S.max' hS_nonempty :=
    S.le_max' F.c
      (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_left F T ρ)
  have hmax_eq :
      S.max' hS_nonempty = F.c :=
    le_antisymm hmax_le hle_max
  calc
    (explicitFormulaRectangleSortedXEndpoints F T ρ).get
        ⟨(explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1,
          Nat.sub_lt
            (explicitFormulaRectangleSortedXEndpoints_length_pos F T ρ)
            Nat.zero_lt_one⟩ =
        S.max' hS_nonempty := by
      exact Finset.sorted_last_eq_max'
    _ = F.c := hmax_eq

/-- Nonnegative rectangle height orders the lower and upper vertical endpoints. -/
theorem explicitFormulaRectangle_verticalEndpointOrder_of_nonneg
    {T : ℝ} (hT_nonneg : 0 ≤ T) :
    -T ≤ T :=
  neg_le_self hT_nonneg

/-- The contour-family horizontal span is traversed from right to left in interval
coordinates because `F.c` lies strictly to the right of `1`. -/
theorem explicitFormulaRectangle_familyHorizontalLower_le_upper
    (F : ExplicitFormulaContourFamily) :
    1 - F.c ≤ F.c :=
  le_of_lt (lt_trans F.one_sub_c_neg F.c_pos)

/-- The right endpoint-data vertical integrand is the named right path integrand after
unfolding the contour-family rectangle. -/
theorem explicitFormulaRectangle_rightEndpointDataIntegrand_eq_rightPath
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T y : ℝ) :
    zetaCompletedExplicitFormulaContourIntegrand f (F.c + y * Complex.I) =
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) y) :=
  rfl

/-- The left endpoint-data vertical integrand is the named left path integrand after
unfolding the contour-family rectangle. -/
theorem explicitFormulaRectangle_leftEndpointDataIntegrand_eq_leftPath
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T y : ℝ) :
    zetaCompletedExplicitFormulaContourIntegrand f ((1 - F.c) + y * Complex.I) =
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) y) :=
  rfl

/-- Left multiplication by the tangent vector `I`, as scalar multiplication, is right
multiplication by `I` for complex-valued line integrals. -/
theorem explicitFormulaRectangle_complexI_smul_eq_mul_right (z : ℂ) :
    Complex.I • z = z * Complex.I := by
  calc
    Complex.I • z = Complex.I * z := by
      exact smul_eq_mul Complex.I z
    _ = z * Complex.I := by
      exact mul_comm Complex.I z

/-- The full right endpoint-data vertical edge is the interval integral over the right
contour path, with scalar tangent normalization. -/
theorem explicitFormulaRectangleOuterRightEndpointDataEdgeIntegral_eq_rightLineIntegral_smul
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT_nonneg : 0 ≤ T) :
    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((-T, T), F.c) =
      Complex.I • zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) := by
  let φ : ℝ → ℂ :=
    fun y : ℝ => zetaCompletedExplicitFormulaContourIntegrand f (F.c + y * Complex.I)
  have hIcc :
      (∫ y in Set.Icc (-T) T, φ y) =
        ∫ y : ℝ in -T..T, φ y :=
    zetaExplicitFormulaSinglePole_setIntegral_Icc_eq_intervalIntegral_of_le
      φ (neg_nonpos.mpr hT_nonneg)
  have hline :
      zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) =
        ∫ y in Set.Icc (-T) T, φ y := by
    rfl
  calc
    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
        f ((-T, T), F.c) =
        Complex.I • (∫ y : ℝ in -T..T, φ y) := by
      exact rfl
    _ = Complex.I • (∫ y in Set.Icc (-T) T, φ y) := by
      exact congrArg (fun z : ℂ => Complex.I • z) hIcc.symm
    _ = Complex.I • zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) := by
      exact congrArg (fun z : ℂ => Complex.I • z) hline.symm

/-- The full left endpoint-data vertical edge is the interval integral over the left
contour path, with scalar tangent normalization. -/
theorem explicitFormulaRectangleOuterLeftEndpointDataEdgeIntegral_eq_leftLineIntegral_smul
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT_nonneg : 0 ≤ T) :
    explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f ((-T, T), 1 - F.c) =
      Complex.I • zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) := by
  let φ : ℝ → ℂ :=
    fun y : ℝ => zetaCompletedExplicitFormulaContourIntegrand f ((1 - F.c) + y * Complex.I)
  have hIcc :
      (∫ y in Set.Icc (-T) T, φ y) =
        ∫ y : ℝ in -T..T, φ y :=
    zetaExplicitFormulaSinglePole_setIntegral_Icc_eq_intervalIntegral_of_le
      φ (neg_nonpos.mpr hT_nonneg)
  have hline :
      zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) =
        ∫ y in Set.Icc (-T) T, φ y := by
    rfl
  calc
    explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
        f ((-T, T), 1 - F.c) =
        Complex.I • (∫ y : ℝ in -T..T, φ y) := by
      exact rfl
    _ = Complex.I • (∫ y in Set.Icc (-T) T, φ y) := by
      exact congrArg (fun z : ℂ => Complex.I • z) hIcc.symm
    _ = Complex.I • zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) := by
      exact congrArg (fun z : ℂ => Complex.I • z) hline.symm

/-- The full bottom endpoint-data horizontal edge is the negative of the named bottom
line integral, because the endpoint-data interval is oriented from right to left. -/
theorem explicitFormulaRectangleOuterBottomEndpointDataEdgeIntegral_eq_neg_bottomLineIntegral_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((F.c, 1 - F.c), -T) =
      -(zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)) := by
  let φ : ℝ → ℂ :=
    fun x : ℝ => zetaCompletedExplicitFormulaContourIntegrand f (x + (-T) * Complex.I)
  let ψ : ℝ → ℂ :=
    fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)
  have horder : 1 - F.c ≤ F.c :=
    explicitFormulaRectangle_familyHorizontalLower_le_upper F
  have hpoint :
      (fun x : ℝ => ψ x) = φ := by
    funext x
    exact congrArg
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaExplicitFormulaOnePole_bottomPath_eq_coordinate F T x)
  have huIcc :
      Set.uIcc F.c (1 - F.c) = Set.Icc (1 - F.c) F.c :=
    Set.uIcc_of_ge horder
  have hset :
      (∫ x in Set.uIcc F.c (1 - F.c), ψ x) =
        ∫ x in Set.Icc (1 - F.c) F.c, φ x := by
    calc
      (∫ x in Set.uIcc F.c (1 - F.c), ψ x) =
          ∫ x in Set.uIcc F.c (1 - F.c), φ x := by
        exact MeasureTheory.setIntegral_congr_fun measurableSet_uIcc
          (fun x _hx => congrFun hpoint x)
      _ = ∫ x in Set.Icc (1 - F.c) F.c, φ x := by
        exact congrArg (fun s : Set ℝ => ∫ x in s, φ x) huIcc
  have hinterval :
      (∫ x in Set.Icc (1 - F.c) F.c, φ x) =
        ∫ x : ℝ in (1 - F.c)..F.c, φ x :=
    zetaExplicitFormulaSinglePole_setIntegral_Icc_eq_intervalIntegral_of_le
      φ horder
  have hline :
      zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) =
        ∫ x : ℝ in (1 - F.c)..F.c, φ x := by
    calc
      zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) =
          ∫ x in Set.uIcc F.c (1 - F.c), ψ x := by
        rfl
      _ = ∫ x in Set.Icc (1 - F.c) F.c, φ x := hset
      _ = ∫ x : ℝ in (1 - F.c)..F.c, φ x := hinterval
  calc
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((F.c, 1 - F.c), -T) =
        ∫ x : ℝ in F.c..(1 - F.c), φ x := by
      exact rfl
    _ = -(∫ x : ℝ in (1 - F.c)..F.c, φ x) := by
      exact intervalIntegral.integral_symm (1 - F.c) F.c
    _ = -(zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)) := by
      exact congrArg Neg.neg hline.symm

/-- The full top endpoint-data horizontal edge is the negative of the named top line
integral, because the endpoint-data interval is oriented from right to left. -/
theorem explicitFormulaRectangleOuterTopEndpointDataEdgeIntegral_eq_neg_topLineIntegral_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f ((F.c, 1 - F.c), T) =
      -(zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)) := by
  let φ : ℝ → ℂ :=
    fun x : ℝ => zetaCompletedExplicitFormulaContourIntegrand f (x + T * Complex.I)
  let ψ : ℝ → ℂ :=
    fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)
  have horder : 1 - F.c ≤ F.c :=
    explicitFormulaRectangle_familyHorizontalLower_le_upper F
  have hpoint :
      (fun x : ℝ => ψ x) = φ := by
    funext x
    exact congrArg
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaExplicitFormulaOnePole_topPath_eq_coordinate F T x)
  have huIcc :
      Set.uIcc F.c (1 - F.c) = Set.Icc (1 - F.c) F.c :=
    Set.uIcc_of_ge horder
  have hset :
      (∫ x in Set.uIcc F.c (1 - F.c), ψ x) =
        ∫ x in Set.Icc (1 - F.c) F.c, φ x := by
    calc
      (∫ x in Set.uIcc F.c (1 - F.c), ψ x) =
          ∫ x in Set.uIcc F.c (1 - F.c), φ x := by
        exact MeasureTheory.setIntegral_congr_fun measurableSet_uIcc
          (fun x _hx => congrFun hpoint x)
      _ = ∫ x in Set.Icc (1 - F.c) F.c, φ x := by
        exact congrArg (fun s : Set ℝ => ∫ x in s, φ x) huIcc
  have hinterval :
      (∫ x in Set.Icc (1 - F.c) F.c, φ x) =
        ∫ x : ℝ in (1 - F.c)..F.c, φ x :=
    zetaExplicitFormulaSinglePole_setIntegral_Icc_eq_intervalIntegral_of_le
      φ horder
  have hline :
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) =
        ∫ x : ℝ in (1 - F.c)..F.c, φ x := by
    calc
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) =
          ∫ x in Set.uIcc F.c (1 - F.c), ψ x := by
        rfl
      _ = ∫ x in Set.Icc (1 - F.c) F.c, φ x := hset
      _ = ∫ x : ℝ in (1 - F.c)..F.c, φ x := hinterval
  calc
    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f ((F.c, 1 - F.c), T) =
        ∫ x : ℝ in F.c..(1 - F.c), φ x := by
      exact rfl
    _ = -(∫ x : ℝ in (1 - F.c)..F.c, φ x) := by
      exact intervalIntegral.integral_symm (1 - F.c) F.c
    _ = -(zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)) := by
      exact congrArg Neg.neg hline.symm

/-- The forward full bottom endpoint-data horizontal edge is the named bottom line
integral.  This is the orientation naturally produced by the sorted horizontal
subdivision, whose adjacent endpoint pairs run from `1 - F.c` to `F.c`. -/
theorem explicitFormulaRectangleOuterBottomEndpointDataEdgeIntegral_forward_eq_bottomLineIntegral_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), -T) =
      zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) := by
  let φ : ℝ → ℂ :=
    fun x : ℝ => zetaCompletedExplicitFormulaContourIntegrand f (x + (-T) * Complex.I)
  let ψ : ℝ → ℂ :=
    fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)
  have horder : 1 - F.c ≤ F.c :=
    explicitFormulaRectangle_familyHorizontalLower_le_upper F
  have hpoint :
      (fun x : ℝ => ψ x) = φ := by
    funext x
    exact congrArg
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaExplicitFormulaOnePole_bottomPath_eq_coordinate F T x)
  have huIcc :
      Set.uIcc F.c (1 - F.c) = Set.Icc (1 - F.c) F.c :=
    Set.uIcc_of_ge horder
  have hset :
      (∫ x in Set.uIcc F.c (1 - F.c), ψ x) =
        ∫ x in Set.Icc (1 - F.c) F.c, φ x := by
    calc
      (∫ x in Set.uIcc F.c (1 - F.c), ψ x) =
          ∫ x in Set.uIcc F.c (1 - F.c), φ x := by
        exact MeasureTheory.setIntegral_congr_fun measurableSet_uIcc
          (fun x _hx => congrFun hpoint x)
      _ = ∫ x in Set.Icc (1 - F.c) F.c, φ x := by
        exact congrArg (fun s : Set ℝ => ∫ x in s, φ x) huIcc
  have hinterval :
      (∫ x in Set.Icc (1 - F.c) F.c, φ x) =
        ∫ x : ℝ in (1 - F.c)..F.c, φ x :=
    zetaExplicitFormulaSinglePole_setIntegral_Icc_eq_intervalIntegral_of_le
      φ horder
  have hline :
      zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) =
        ∫ x : ℝ in (1 - F.c)..F.c, φ x := by
    calc
      zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) =
          ∫ x in Set.uIcc F.c (1 - F.c), ψ x := by
        rfl
      _ = ∫ x in Set.Icc (1 - F.c) F.c, φ x := hset
      _ = ∫ x : ℝ in (1 - F.c)..F.c, φ x := hinterval
  calc
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), -T) =
        ∫ x : ℝ in (1 - F.c)..F.c, φ x := by
      exact rfl
    _ = zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) := by
      exact hline.symm

/-- The forward full top endpoint-data horizontal edge is the named top line integral.
This is the orientation naturally produced by the sorted horizontal subdivision. -/
theorem explicitFormulaRectangleOuterTopEndpointDataEdgeIntegral_forward_eq_topLineIntegral_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), T) =
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) := by
  let φ : ℝ → ℂ :=
    fun x : ℝ => zetaCompletedExplicitFormulaContourIntegrand f (x + T * Complex.I)
  let ψ : ℝ → ℂ :=
    fun x : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)
  have horder : 1 - F.c ≤ F.c :=
    explicitFormulaRectangle_familyHorizontalLower_le_upper F
  have hpoint :
      (fun x : ℝ => ψ x) = φ := by
    funext x
    exact congrArg
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaExplicitFormulaOnePole_topPath_eq_coordinate F T x)
  have huIcc :
      Set.uIcc F.c (1 - F.c) = Set.Icc (1 - F.c) F.c :=
    Set.uIcc_of_ge horder
  have hset :
      (∫ x in Set.uIcc F.c (1 - F.c), ψ x) =
        ∫ x in Set.Icc (1 - F.c) F.c, φ x := by
    calc
      (∫ x in Set.uIcc F.c (1 - F.c), ψ x) =
          ∫ x in Set.uIcc F.c (1 - F.c), φ x := by
        exact MeasureTheory.setIntegral_congr_fun measurableSet_uIcc
          (fun x _hx => congrFun hpoint x)
      _ = ∫ x in Set.Icc (1 - F.c) F.c, φ x := by
        exact congrArg (fun s : Set ℝ => ∫ x in s, φ x) huIcc
  have hinterval :
      (∫ x in Set.Icc (1 - F.c) F.c, φ x) =
        ∫ x : ℝ in (1 - F.c)..F.c, φ x :=
    zetaExplicitFormulaSinglePole_setIntegral_Icc_eq_intervalIntegral_of_le
      φ horder
  have hline :
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) =
        ∫ x : ℝ in (1 - F.c)..F.c, φ x := by
    calc
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) =
          ∫ x in Set.uIcc F.c (1 - F.c), ψ x := by
        rfl
      _ = ∫ x in Set.Icc (1 - F.c) F.c, φ x := hset
      _ = ∫ x : ℝ in (1 - F.c)..F.c, φ x := hinterval
  calc
    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
        f ((1 - F.c, F.c), T) =
        ∫ x : ℝ in (1 - F.c)..F.c, φ x := by
      exact rfl
    _ = zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) := by
      exact hline.symm

/-- Bottom horizontal coordinate labels selected from one fixed horizontal adjacent-pair
row, with the same coordinate-omission filter as the selected cell list. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
