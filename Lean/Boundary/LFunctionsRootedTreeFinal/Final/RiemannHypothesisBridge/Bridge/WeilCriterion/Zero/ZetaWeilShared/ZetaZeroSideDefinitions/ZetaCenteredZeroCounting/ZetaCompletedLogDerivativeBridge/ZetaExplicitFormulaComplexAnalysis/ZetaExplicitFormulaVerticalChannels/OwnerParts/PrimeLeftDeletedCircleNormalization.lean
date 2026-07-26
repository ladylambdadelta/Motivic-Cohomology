import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftResidueFreeFiniteRectangle

/-!
# Prime-left deleted-circle normalization

This file owns the sign and orientation algebra for the deleted-circle term in
the prime-left residue-free boundary identity.  The raw deleted-circle boundary
sum is a residue-window term; this file only transports that raw limit through
the `finiteExcisionError = - rawDeletedCircleBoundarySum` convention and the
prime-left multiplication by `I`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The combined prime-left deleted-circle orientation kills a zero raw
deleted-circle limit. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_I_mul_neg_zero :
    Complex.I * (-(0 : ℂ)) = 0 := by
  calc
    Complex.I * (-(0 : ℂ)) = Complex.I * (0 : ℂ) := by
      exact congrArg (fun z : ℂ => Complex.I * z) (neg_zero : -(0 : ℂ) = 0)
    _ = 0 := by
      exact mul_zero Complex.I

/-- The finite prime-left excision convention is the negative raw
deleted-circle boundary sum. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError_eq_neg_rawDeletedCircleBoundarySum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
        f T ε =
      -explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε :=
  Eq.refl _

/-- Scheduled deleted-circle excision error for the residue-free left-prime
contour after the prime-left orientation conversion. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ) (u : ℝ) :
    ℂ :=
  Complex.I *
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
      f (h.height_schedule.height u) (ε u)

/-- A raw deleted-circle boundary limit transports to the finite prime-left
excision convention with a minus sign. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError_tendsto_neg_of_rawDeletedCircleBoundarySum
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι}
    (f : ZetaAdmissibleFunction) (T ε : ι → ℝ) (R : ℂ)
    (hraw :
      Tendsto
        (fun i : ι =>
          explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (T i) (ε i))
        l
        (𝓝 R)) :
    Tendsto
      (fun i : ι =>
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
          f (T i) (ε i))
      l
      (𝓝 (-R)) := by
  have hneg :
      Tendsto
        (fun i : ι =>
          -explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (T i) (ε i))
        l
        (𝓝 (-R)) :=
    hraw.neg
  have hfun :
      (fun i : ι =>
        zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
          f (T i) (ε i)) =
      fun i : ι =>
        -explicitFormulaRectangleRawDeletedCircleBoundarySum
          f (T i) (ε i) := by
    funext i
    exact
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError_eq_neg_rawDeletedCircleBoundarySum
        f (T i) (ε i)
  exact
    Eq.subst
      (motive := fun φ : ι → ℂ =>
        Tendsto φ l (𝓝 (-R)))
      hfun.symm
      hneg

/-- The scheduled prime-left excision packet is `I` times the finite excision
term at the scheduled height and radius. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_eq_I_mul_finiteExcisionError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε =
      fun u : ℝ =>
        Complex.I *
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
            f (h.height_schedule.height u) (ε u) := by
  funext u
  exact Eq.refl _

/-- A finite-excision limit transports to the scheduled prime-left excision
packet after multiplication by the contour orientation factor `I`. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_I_mul_of_finiteExcisionError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ) (E : ℂ)
    (hfinite :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
            f (h.height_schedule.height u) (ε u))
        atTop
        (𝓝 E)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      atTop
      (𝓝 (Complex.I * E)) := by
  have hmul :
      Tendsto
        (fun u : ℝ =>
          Complex.I *
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
              f (h.height_schedule.height u) (ε u))
        atTop
        (𝓝 (Complex.I * E)) :=
    tendsto_const_nhds.mul hfinite
  have hfun :
      zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h ε =
        fun u : ℝ =>
          Complex.I *
            zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
              f (h.height_schedule.height u) (ε u) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_eq_I_mul_finiteExcisionError
      f F h ε
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 (Complex.I * E)))
      hfun.symm
      hmul

/-- A raw deleted-circle boundary limit transports directly to the scheduled
prime-left excision packet with the combined orientation `-I`. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_neg_I_mul_of_rawDeletedCircleBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ) (R : ℂ)
    (hraw :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u))
        atTop
        (𝓝 R)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      atTop
      (𝓝 (Complex.I * (-R))) := by
  have hfinite :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError
            f (h.height_schedule.height u) (ε u))
        atTop
        (𝓝 (-R)) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_finiteExcisionError_tendsto_neg_of_rawDeletedCircleBoundarySum
      f h.height_schedule.height ε R hraw
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_I_mul_of_finiteExcisionError
      f F h ε (-R) hfinite

/-- Eventual scheduled raw deleted-circle equality gives the corresponding
raw deleted-circle limit. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_rawDeletedCircleBoundarySum_tendsto_of_eventually_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (R : ℂ)
    (heventually :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u) =
          R) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaRectangleRawDeletedCircleBoundarySum
          f (h.height_schedule.height u) (ε u))
      atTop
      (𝓝 R) := by
  have hconstant : Tendsto (fun _ : ℝ => R) atTop (𝓝 R) :=
    tendsto_const_nhds
  exact
    hconstant.congr'
      (heventually.mono
        (fun _ hu => hu.symm))

/-- Eventual scheduled raw deleted-circle equality transports to the scheduled
prime-left excision packet with the combined `-I` orientation. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_neg_I_mul_of_eventually_rawDeletedCircleBoundarySum_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (R : ℂ)
    (heventually :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u) =
          R) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      atTop
      (𝓝 (Complex.I * (-R))) := by
  have hraw :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u))
        atTop
        (𝓝 R) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_rawDeletedCircleBoundarySum_tendsto_of_eventually_eq
      f F h ε R heventually
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_neg_I_mul_of_rawDeletedCircleBoundarySum
      f F h ε R hraw

/-- If the scheduled raw deleted-circle residue packet is eventually zero,
then the oriented scheduled prime-left excision packet tends to zero. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_zero_of_eventually_rawDeletedCircleBoundarySum_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (heventually :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u) =
          0) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      atTop
      (𝓝 0) := by
  have hlimit :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h ε)
        atTop
        (𝓝 (Complex.I * (-0))) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_neg_I_mul_of_eventually_rawDeletedCircleBoundarySum_eq
      f F h ε 0 heventually
  have hzero : Complex.I * (-0 : ℂ) = 0 := by
    exact zetaCompletedExplicitFormulaPrimeLeftResidueFree_I_mul_neg_zero
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h ε)
          atTop
          (𝓝 z))
      hzero
      hlimit

/-- If the scheduled raw deleted-circle residue packet tends to zero, then
the oriented scheduled prime-left excision packet tends to zero. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_zero_of_rawDeletedCircleBoundarySum_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (hraw :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u))
        atTop
        (𝓝 0)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      atTop
      (𝓝 0) := by
  have hlimit :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h ε)
        atTop
        (𝓝 (Complex.I * (-0))) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_neg_I_mul_of_rawDeletedCircleBoundarySum
      f F h ε 0 hraw
  have hzero : Complex.I * (-0 : ℂ) = 0 := by
    exact zetaCompletedExplicitFormulaPrimeLeftResidueFree_I_mul_neg_zero
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h ε)
          atTop
          (𝓝 z))
      hzero
      hlimit

/-- A raw deleted-circle boundary limit equal to a residue-window packet
transports to the exact oriented prime-left excision limit.

This is the nonzero form used before any residue-window cancellation has been
performed.  The zero-specialized lemmas above should only be used after the
raw residue-window contribution has genuinely been shown to cancel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_orientedResidueWindow_of_rawDeletedCircleBoundarySum_tendsto
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (R : ℂ)
    (hraw :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u))
        atTop
        (𝓝 R)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      atTop
      (𝓝 (Complex.I * (-R))) :=
  zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_neg_I_mul_of_rawDeletedCircleBoundarySum
    f F h ε R hraw

/-- Finite raw deleted-circle boundary sum with the local residue-theorem
normalization.

If every raw singular coordinate has deleted-circle value `2πi` times its
indexed residue, then the whole finite raw deleted-circle sum is `2πi` times
the indexed raw singular residue sum.  This is purely finite-carrier algebra:
the analytic residue theorem supplies the three value hypotheses. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_twoPiI_smul_indexedResidueSum_of_values
    (f : ZetaAdmissibleFunction) (T ε : ℝ)
    (hzero :
      explicitFormulaRectangleRawDeletedCircleBoundary f ε 0 =
        (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangle_zeroPoleResidue f)
    (hone :
      explicitFormulaRectangleRawDeletedCircleBoundary f ε 1 =
        (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangle_onePoleResidue f)
    (hcompleted :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
          explicitFormulaRectangleRawDeletedCircleBoundary f ε
              (completedZeroResidueCoordinate ρ) =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaZeroResidue f
                (explicitFormulaZeroDataOfCompletedZero ρ)) :
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangleRawSingularIndexedResidueSum f T := by
  let c : ℂ := 2 * ↑Real.pi * Complex.I
  let C : Finset ℂ := explicitFormulaCompletedZeroWindowCoordinates T
  let W : Finset {ρ : ℂ // ZetaCompletedZero ρ} :=
    explicitFormulaCompletedZeroContourHeightWindow T
  let deletedCircle : ℂ → ℂ :=
    explicitFormulaRectangleRawDeletedCircleBoundary f ε
  have hzero_not_C : (0 : ℂ) ∉ C := by
    intro hmem
    exact
      Exists.elim
        (explicitFormulaCompletedZeroWindowCoordinates_exists_window_of_mem T hmem)
        (fun ρ hρ =>
          (completedZeroResidueCoordinate_ne_zero ρ) hρ.right)
  have hone_not_C : (1 : ℂ) ∉ C := by
    intro hmem
    exact
      Exists.elim
        (explicitFormulaCompletedZeroWindowCoordinates_exists_window_of_mem T hmem)
        (fun ρ hρ =>
          (completedZeroResidueCoordinate_ne_one ρ) hρ.right)
  have hzero_ne_one : (0 : ℂ) ≠ 1 :=
    zero_ne_one
  have hzero_not_insert : (0 : ℂ) ∉ insert (1 : ℂ) C := by
    intro hmem
    match Finset.mem_insert.mp hmem with
    | Or.inl h01 =>
        exact hzero_ne_one h01
    | Or.inr h0C =>
        exact hzero_not_C h0C
  have hone_not_insert_base : (1 : ℂ) ∉ C :=
    hone_not_C
  have himage :
      (∑ z in C, deletedCircle z) =
        ∑ ρ in W, deletedCircle (completedZeroResidueCoordinate ρ) := by
    exact
      Finset.sum_image
        (s := W)
        (f := fun z : ℂ => deletedCircle z)
        (g := fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          completedZeroResidueCoordinate ρ)
        (fun ρ _hρ σ _hσ hcoord =>
          completedZeroResidueCoordinate_injective hcoord)
  let Z : ℂ := explicitFormulaRectangle_zeroPoleResidue f
  let O : ℂ := explicitFormulaRectangle_onePoleResidue f
  let R : ℂ :=
    ∑ ρ in W,
      explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)
  have hcompleted_sum :
      (∑ ρ in W, deletedCircle (completedZeroResidueCoordinate ρ)) =
        ∑ ρ in W,
          c • explicitFormulaZeroResidue f
            (explicitFormulaZeroDataOfCompletedZero ρ) := by
    exact
      Finset.sum_congr rfl
        (fun ρ hρ => hcompleted ρ hρ)
  have hcompleted_scaled :
      (∑ ρ in W,
          c • explicitFormulaZeroResidue f
            (explicitFormulaZeroDataOfCompletedZero ρ)) =
        c • R := by
    exact (Finset.smul_sum).symm
  have hscaled :
      c • Z + (c • O + c • R) =
        c • (Z + O + R) := by
    calc
      c • Z + (c • O + c • R) =
          c • Z + c • (O + R) := by
        exact congrArg (fun x : ℂ => c • Z + x) (smul_add c O R).symm
      _ = c • (Z + (O + R)) := by
        exact (smul_add c Z (O + R)).symm
      _ = c • (Z + O + R) := by
        exact congrArg (fun x : ℂ => c • x) (add_assoc Z O R).symm
  calc
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T)
          deletedCircle := by
      rfl
    _ = ∑ z in insert (0 : ℂ) (insert (1 : ℂ) C), deletedCircle z := by
      rfl
    _ = deletedCircle 0 + ∑ z in insert (1 : ℂ) C, deletedCircle z := by
      exact Finset.sum_insert hzero_not_insert
    _ = deletedCircle 0 + (deletedCircle 1 + ∑ z in C, deletedCircle z) := by
      exact congrArg
        (fun x : ℂ => deletedCircle 0 + x)
        (Finset.sum_insert hone_not_insert_base)
    _ = c • Z + (deletedCircle 1 + ∑ z in C, deletedCircle z) := by
      exact congrArg
        (fun x : ℂ => x + (deletedCircle 1 + ∑ z in C, deletedCircle z))
        hzero
    _ = c • Z + (c • O + ∑ z in C, deletedCircle z) := by
      exact congrArg
        (fun x : ℂ => c • Z + (x + ∑ z in C, deletedCircle z))
        hone
    _ = c • Z +
          (c • O + ∑ ρ in W, deletedCircle (completedZeroResidueCoordinate ρ)) := by
      exact congrArg (fun x : ℂ => c • Z + (c • O + x)) himage
    _ = c • Z +
          (c • O +
            ∑ ρ in W,
              c • explicitFormulaZeroResidue f
                (explicitFormulaZeroDataOfCompletedZero ρ)) := by
      exact congrArg (fun x : ℂ => c • Z + (c • O + x)) hcompleted_sum
    _ = c • Z + (c • O + c • R) := by
      exact congrArg (fun x : ℂ => c • Z + (c • O + x)) hcompleted_scaled
    _ = c • (Z + O + R) := by
      exact hscaled
    _ =
        (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangleRawSingularIndexedResidueSum f T := by
      have hindexed :
          Z + O + R =
            explicitFormulaRectangleRawSingularIndexedResidueSum f T :=
        Eq.refl _
      calc
        c • (Z + O + R) =
            c • explicitFormulaRectangleRawSingularIndexedResidueSum f T := by
          exact congrArg (fun value : ℂ => c • value) hindexed
        _ =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaRectangleRawSingularIndexedResidueSum f T := by
          exact Eq.refl _

/-- Multiplicative-notation wrapper for
`explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_twoPiI_smul_indexedResidueSum_of_values`. -/
theorem explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_twoPiI_mul_indexedResidueSum_of_values
    (f : ZetaAdmissibleFunction) (T ε : ℝ)
    (hzero :
      explicitFormulaRectangleRawDeletedCircleBoundary f ε 0 =
        (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangle_zeroPoleResidue f)
    (hone :
      explicitFormulaRectangleRawDeletedCircleBoundary f ε 1 =
        (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangle_onePoleResidue f)
    (hcompleted :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∀ _hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
          explicitFormulaRectangleRawDeletedCircleBoundary f ε
              (completedZeroResidueCoordinate ρ) =
            (2 * ↑Real.pi * Complex.I : ℂ) •
              explicitFormulaZeroResidue f
                (explicitFormulaZeroDataOfCompletedZero ρ)) :
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε =
      (2 * ↑Real.pi * Complex.I : ℂ) *
        explicitFormulaRectangleRawSingularIndexedResidueSum f T := by
  have hsmul :
      explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε =
        (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangleRawSingularIndexedResidueSum f T :=
    explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_twoPiI_smul_indexedResidueSum_of_values
      f T ε hzero hone hcompleted
  calc
    explicitFormulaRectangleRawDeletedCircleBoundarySum f T ε =
        (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangleRawSingularIndexedResidueSum f T := hsmul
    _ =
        (2 * ↑Real.pi * Complex.I : ℂ) *
          explicitFormulaRectangleRawSingularIndexedResidueSum f T := by
      rfl

/-- Eventual scheduled local deleted-circle residue values give the scheduled
raw deleted-circle sum equality with the finite-rectangle `2πi`
normalization. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_eventually_rawDeletedCircleBoundarySum_eq_twoPiI_mul_indexedResidue_of_eventually_values
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (hzero :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundary f (ε u) 0 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_zeroPoleResidue f)
    (hone :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundary f (ε u) 1 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_onePoleResidue f)
    (hcompleted :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∀ _hρ : ρ ∈
              explicitFormulaCompletedZeroContourHeightWindow
                (h.height_schedule.height u),
            explicitFormulaRectangleRawDeletedCircleBoundary f (ε u)
                (completedZeroResidueCoordinate ρ) =
              (2 * ↑Real.pi * Complex.I : ℂ) •
                explicitFormulaZeroResidue f
                  (explicitFormulaZeroDataOfCompletedZero ρ)) :
    ∀ᶠ u in atTop,
      explicitFormulaRectangleRawDeletedCircleBoundarySum
          f (h.height_schedule.height u) (ε u) =
        (2 * ↑Real.pi * Complex.I : ℂ) *
          explicitFormulaRectangleRawSingularIndexedResidueSum
            f (h.height_schedule.height u) := by
  exact
    (hzero.and (hone.and hcompleted)).mono
      (fun u hu =>
        match hu with
        | ⟨hzero_u, ⟨hone_u, hcompleted_u⟩⟩ =>
            explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_twoPiI_mul_indexedResidueSum_of_values
              f (h.height_schedule.height u) (ε u)
              hzero_u hone_u hcompleted_u)

/-- Scheduled raw deleted-circle equality to the finite indexed residue sum,
with the local residue-theorem factor `2πi`, gives the corresponding raw
deleted-circle limit.

This is the honest bridge between the fixed finite-rectangle deleted-circle
residue calculation and a scheduled-height contour packet.  It keeps the
`2πi` factor explicit; downstream cancellation must account for this
normalization rather than treating the raw deleted-circle packet as zero. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_rawDeletedCircleBoundarySum_tendsto_twoPiI_mul_indexedResidue_of_eventually_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (R : ℂ)
    (hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleRawSingularIndexedResidueSum
            f (h.height_schedule.height u))
        atTop
        (𝓝 R))
    (heventually :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u) =
          (2 * ↑Real.pi * Complex.I : ℂ) *
            explicitFormulaRectangleRawSingularIndexedResidueSum
              f (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaRectangleRawDeletedCircleBoundarySum
          f (h.height_schedule.height u) (ε u))
      atTop
      (𝓝 ((2 * ↑Real.pi * Complex.I : ℂ) * R)) := by
  have hscaled :
      Tendsto
        (fun u : ℝ =>
          (2 * ↑Real.pi * Complex.I : ℂ) *
            explicitFormulaRectangleRawSingularIndexedResidueSum
              f (h.height_schedule.height u))
        atTop
        (𝓝 ((2 * ↑Real.pi * Complex.I : ℂ) * R)) :=
    tendsto_const_nhds.mul hresidue
  exact
    hscaled.congr'
      (heventually.mono
        (fun _ hu => hu.symm))

/-- Scheduled raw deleted-circle equality to the finite indexed residue sum
transports through the prime-left excision orientation.

If the indexed residue window tends to `R`, then the scheduled prime-left
excision packet tends to `I * (-(2πi * R))`.  This is the nonzero packet that
must later be paired with the matching residue-window contribution. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_twoPiI_orientedIndexedResidue_of_eventually_rawDeletedCircleBoundarySum_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (R : ℂ)
    (hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleRawSingularIndexedResidueSum
            f (h.height_schedule.height u))
        atTop
        (𝓝 R))
    (heventually :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u) =
          (2 * ↑Real.pi * Complex.I : ℂ) *
            explicitFormulaRectangleRawSingularIndexedResidueSum
              f (h.height_schedule.height u)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      atTop
      (𝓝 (Complex.I * (-((2 * ↑Real.pi * Complex.I : ℂ) * R)))) := by
  have hraw :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u))
        atTop
        (𝓝 ((2 * ↑Real.pi * Complex.I : ℂ) * R)) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_rawDeletedCircleBoundarySum_tendsto_twoPiI_mul_indexedResidue_of_eventually_eq
      f F h ε R hresidue heventually
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_neg_I_mul_of_rawDeletedCircleBoundarySum
      f F h ε ((2 * ↑Real.pi * Complex.I : ℂ) * R) hraw

/-- If the scheduled indexed residue packet vanishes and the raw deleted-circle
sum has the finite-rectangle `2πi` residue normalization, then the scheduled
prime-left excision packet tends to zero.

This is the safe zero-limit form: it requires the residue-window packet itself
to vanish, instead of assuming the raw deleted-circle boundary is zero. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_zero_of_indexedResidue_tendsto_zero_and_eventually_rawDeletedCircleBoundarySum_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleRawSingularIndexedResidueSum
            f (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (heventually :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u) =
          (2 * ↑Real.pi * Complex.I : ℂ) *
            explicitFormulaRectangleRawSingularIndexedResidueSum
              f (h.height_schedule.height u)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      atTop
      (𝓝 0) := by
  have hlimit :
      Tendsto
        (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
          f F h ε)
        atTop
        (𝓝 (Complex.I * (-((2 * ↑Real.pi * Complex.I : ℂ) * 0)))) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_twoPiI_orientedIndexedResidue_of_eventually_rawDeletedCircleBoundarySum_eq
      f F h ε 0 hresidue heventually
  have hmul_zero :
      (2 * ↑Real.pi * Complex.I : ℂ) * 0 = 0 :=
    mul_zero (2 * ↑Real.pi * Complex.I : ℂ)
  have hneg_zero :
      -((2 * ↑Real.pi * Complex.I : ℂ) * 0) = 0 := by
    calc
      -((2 * ↑Real.pi * Complex.I : ℂ) * 0) = -(0 : ℂ) := by
        exact congrArg (fun z : ℂ => -z) hmul_zero
      _ = 0 := by
        exact neg_zero
  have horiented_zero :
      Complex.I * (-((2 * ↑Real.pi * Complex.I : ℂ) * 0)) = 0 := by
    calc
      Complex.I * (-((2 * ↑Real.pi * Complex.I : ℂ) * 0)) =
          Complex.I * 0 := by
        exact congrArg (fun z : ℂ => Complex.I * z) hneg_zero
      _ = 0 := by
        exact mul_zero Complex.I
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
            f F h ε)
          atTop
          (𝓝 z))
      horiented_zero
      hlimit

/-- Scheduled excision zero from the true local deleted-circle residue values
and vanishing of the scheduled indexed residue packet. -/
theorem zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_zero_of_indexedResidue_tendsto_zero_and_eventually_values
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (ε : ℝ → ℝ)
    (hresidue :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleRawSingularIndexedResidueSum
            f (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (hzero :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundary f (ε u) 0 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_zeroPoleResidue f)
    (hone :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundary f (ε u) 1 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_onePoleResidue f)
    (hcompleted :
      ∀ᶠ u in atTop,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∀ _hρ : ρ ∈
              explicitFormulaCompletedZeroContourHeightWindow
                (h.height_schedule.height u),
            explicitFormulaRectangleRawDeletedCircleBoundary f (ε u)
                (completedZeroResidueCoordinate ρ) =
              (2 * ↑Real.pi * Complex.I : ℂ) •
                explicitFormulaZeroResidue f
                  (explicitFormulaZeroDataOfCompletedZero ρ)) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError
        f F h ε)
      atTop
      (𝓝 0) := by
  have heventually :
      ∀ᶠ u in atTop,
        explicitFormulaRectangleRawDeletedCircleBoundarySum
            f (h.height_schedule.height u) (ε u) =
          (2 * ↑Real.pi * Complex.I : ℂ) *
            explicitFormulaRectangleRawSingularIndexedResidueSum
              f (h.height_schedule.height u) :=
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_eventually_rawDeletedCircleBoundarySum_eq_twoPiI_mul_indexedResidue_of_eventually_values
      f F h ε hzero hone hcompleted
  exact
    zetaCompletedExplicitFormulaPrimeLeftResidueFree_scheduledExcisionError_tendsto_zero_of_indexedResidue_tendsto_zero_and_eventually_rawDeletedCircleBoundarySum_eq
      f F h ε hresidue heventually

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
