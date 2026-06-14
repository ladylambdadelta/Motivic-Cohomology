import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaCompletedPositiveBoundary.ZetaCompletedLowerWeight.RealSymmetricPSDRadical.Owner

/-!
# Completed lower-weight exact boundary layer

This file owns the finite and completed lower-weight exact components, their
Hilbert stream realization, and the radical/nullity API consumed by the positive
boundary descent.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The finite lower-weight exact component consisting of diagonal debt plus its absorption
channel.  Its finite-part representative is identically zero. -/
def finiteBoundaryLowerWeightExactObject
    (N : ℕ) (f : ZetaAdmissibleFunction) : FiniteBoundaryWeightObject :=
  { positiveSquare := 0
    primeCross := 0
    diagonalDebt := zetaPrimeDiagonalDebt N f
    debtAbsorption := finitePartDebtAbsorptionWindow N f
    archCorrection := 0 }

/-- A finite boundary packet is lower-weight exact when its finite-part representative is
zero. -/
structure FiniteBoundaryLowerWeightExactCert
    (x : FiniteBoundaryWeightObject) where
  finitePart_eq_zero :
    FiniteBoundaryWeightObject.finitePartRepresentative x = 0

/-- The concrete diagonal-debt plus debt-absorption packet is finite lower-weight exact. -/
def finiteBoundaryLowerWeightExactObject_cert
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryLowerWeightExactCert
      (finiteBoundaryLowerWeightExactObject N f) :=
  { finitePart_eq_zero := by
      unfold finiteBoundaryLowerWeightExactObject
      unfold FiniteBoundaryWeightObject.finitePartRepresentative
      unfold finitePartDebtAbsorptionWindow
      let D : ℝ := zetaPrimeDiagonalDebt N f
      change 0 + D + -D + 0 = 0
      calc
        0 + D + -D + 0 = D + -D + 0 := by
          exact congrArg (fun x : ℝ => x + -D + 0) (zero_add D)
        _ = 0 + 0 := by
          exact congrArg (fun x : ℝ => x + 0) (add_neg_cancel D)
        _ = 0 := by
          exact zero_add 0 }

/-- A completed boundary stream realized in the Hilbert pairing. -/
structure CompletedBoundaryHilbertWeightStream where
  source : CompletedBoundaryHilbertSource
  object : ℕ → FiniteBoundaryWeightObject
  scalar : ℝ
  scalar_eq_pairing_self :
    scalar = completedBoundaryHilbertPairing source source
  finitePart_tendsto_scalar :
    Tendsto
      (fun N : ℕ =>
        FiniteBoundaryWeightObject.finitePartRepresentative (object N))
      atTop
      (𝓝 scalar)

namespace CompletedBoundaryHilbertWeightStream

/-- A Hilbert stream is lower-weight exact when its scalar realization is zero. -/
def IsLowerWeightExact
    (D : CompletedBoundaryHilbertWeightStream) : Prop :=
  D.scalar = 0

/-- A Hilbert stream is lower-weight null when it lies in the radical of the Hilbert pairing. -/
def IsLowerWeightNull
    (D : CompletedBoundaryHilbertWeightStream) : Prop :=
  ∀ T : CompletedBoundaryHilbertWeightStream,
    completedBoundaryHilbertPairing D.source T.source = 0 ∧
      completedBoundaryHilbertPairing T.source D.source = 0

/-- Lower-weight exactness gives diagonal nullity in the Hilbert pairing. -/
theorem IsLowerWeightExact.pairing_self_eq_zero
    {D : CompletedBoundaryHilbertWeightStream}
    (hD : IsLowerWeightExact D) :
    completedBoundaryHilbertPairing D.source D.source = 0 := by
  exact D.scalar_eq_pairing_self.symm.trans hD

end CompletedBoundaryHilbertWeightStream

/-- The completed Hilbert weight stream attached to an admissible seed. -/
def completedBoundaryHilbertWeightStream
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertWeightStream :=
  { source := completedBoundaryHilbertSource f
    object := fun N : ℕ => finiteBoundaryWeightObject N f
    scalar := Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))
    scalar_eq_pairing_self :=
      (completedBoundaryHilbertPairing_source_self_eq_boundaryChannel_re f).symm
    finitePart_tendsto_scalar := by
      have hfinite :
          Tendsto
            (fun N : ℕ => finitePartBoundaryWindow N f)
            atTop
            (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) :=
        finitePartBoundaryWindow_tendsto_boundaryChannel f
      have hobject :
          (fun N : ℕ =>
            FiniteBoundaryWeightObject.finitePartRepresentative
              (finiteBoundaryWeightObject N f)) =
            (fun N : ℕ => finitePartBoundaryWindow N f) := by
        funext N
        exact finiteBoundaryWeightObject_finitePartRepresentative_eq_finitePartBoundaryWindow
          N f
      exact Eq.subst
        (motive := fun u : ℕ → ℝ =>
          Tendsto u atTop
            (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))))
        hobject.symm
        hfinite }

/-- The finite lower-weight exact component has zero finite-part representative. -/
theorem finiteBoundaryLowerWeightExactObject_finitePart_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryLowerWeightExactObject N f) =
      0 :=
  (finiteBoundaryLowerWeightExactObject_cert N f).finitePart_eq_zero

/-- The completed lower-weight exact stream has zero finite-part representatives. -/
theorem completedBoundaryLowerWeightExact_finitePart_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryLowerWeightExactObject N f) =
      0 :=
  finiteBoundaryLowerWeightExactObject_finitePart_eq_zero N f

/-- The concrete source-probe package for the lower-weight exact diagonal-debt cancellation
component.  It records the actual Hilbert source and the actual finite window component; no
cross-pairing vanishing is built into this object. -/
structure CompletedBoundaryLowerWeightExactSourceProbe
    (f : ZetaAdmissibleFunction) where
  source : CompletedBoundaryHilbertSource
  object : ℕ → FiniteBoundaryWeightObject
  source_eq_zero :
    source = completedBoundaryLowerWeightExactHilbertSource
  object_eq_exact :
    object = fun N : ℕ => finiteBoundaryLowerWeightExactObject N f
  finitePart_eq_zero :
    ∀ N : ℕ,
      FiniteBoundaryWeightObject.finitePartRepresentative (object N) = 0

/-- The diagonal-debt plus debt-absorption cancellation packet is represented by the zero
Hilbert source at the finite-window level. -/
def completedBoundaryLowerWeightExactSourceProbe
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryLowerWeightExactSourceProbe f :=
  { source := completedBoundaryLowerWeightExactHilbertSource
    object := fun N : ℕ => finiteBoundaryLowerWeightExactObject N f
    source_eq_zero := rfl
    object_eq_exact := rfl
    finitePart_eq_zero := by
      intro N
      exact finiteBoundaryLowerWeightExactObject_finitePart_eq_zero N f }

/-- The lower-weight exact source probe has zero finite scalar at every cutoff. -/
theorem completedBoundaryLowerWeightExactSourceProbe_finitePart_eq_zero
    (f : ZetaAdmissibleFunction) (N : ℕ) :
    FiniteBoundaryWeightObject.finitePartRepresentative
        ((completedBoundaryLowerWeightExactSourceProbe f).object N) =
      0 :=
  (completedBoundaryLowerWeightExactSourceProbe f).finitePart_eq_zero N

/-- The completed Hilbert stream represented by the lower-weight exact diagonal-debt
cancellation component. -/
def completedBoundaryLowerWeightExactHilbertWeightStream
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertWeightStream :=
  { source := (completedBoundaryLowerWeightExactSourceProbe f).source
    object := (completedBoundaryLowerWeightExactSourceProbe f).object
    scalar := 0
    scalar_eq_pairing_self := by
      have hsource :
          (completedBoundaryLowerWeightExactSourceProbe f).source =
            (0 : CompletedBoundaryHilbertSource) :=
        (completedBoundaryLowerWeightExactSourceProbe f).source_eq_zero
      change
        0 =
          completedBoundaryHilbertPairing
            (completedBoundaryLowerWeightExactSourceProbe f).source
            (completedBoundaryLowerWeightExactSourceProbe f).source
      calc
        0 =
            completedBoundaryHilbertPairing
              (0 : CompletedBoundaryHilbertSource)
              (0 : CompletedBoundaryHilbertSource) := by
          exact completedBoundaryHilbertPairing_zero_zero.symm
        _ =
            completedBoundaryHilbertPairing
              (completedBoundaryLowerWeightExactSourceProbe f).source
              (completedBoundaryLowerWeightExactSourceProbe f).source := by
          exact congrArg₂ completedBoundaryHilbertPairing hsource.symm hsource.symm
    finitePart_tendsto_scalar := by
      have hzero :
          (fun N : ℕ =>
            FiniteBoundaryWeightObject.finitePartRepresentative
              ((completedBoundaryLowerWeightExactSourceProbe f).object N)) =
            fun _N : ℕ => 0 := by
        funext N
        exact completedBoundaryLowerWeightExactSourceProbe_finitePart_eq_zero f N
      exact Eq.subst
        (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
        hzero.symm
        tendsto_const_nhds }

/-- The lower-weight exact Hilbert stream has zero scalar. -/
theorem completedBoundaryLowerWeightExactHilbertWeightStream_scalar_eq_zero
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryLowerWeightExactHilbertWeightStream f).scalar = 0 := by
  rfl

/-- The lower-weight exact Hilbert stream is lower-weight exact. -/
theorem completedBoundaryLowerWeightExactHilbertWeightStream_isLowerWeightExact
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightExact
      (completedBoundaryLowerWeightExactHilbertWeightStream f) := by
  rfl

/-- Any completed Hilbert stream with zero source is lower-weight null. -/
theorem completedBoundaryHilbertWeightStream_isLowerWeightNull_of_source_eq_zero
    (D : CompletedBoundaryHilbertWeightStream)
    (hD : D.source = (0 : CompletedBoundaryHilbertSource)) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightNull D := by
  intro T
  constructor
  · calc
      completedBoundaryHilbertPairing D.source T.source =
          completedBoundaryHilbertPairing (0 : CompletedBoundaryHilbertSource) T.source := by
        exact congrArg (fun X : CompletedBoundaryHilbertSource =>
          completedBoundaryHilbertPairing X T.source) hD
      _ = 0 := by
        exact completedBoundaryHilbertPairing_zero_left T.source
  · calc
      completedBoundaryHilbertPairing T.source D.source =
          completedBoundaryHilbertPairing T.source (0 : CompletedBoundaryHilbertSource) := by
        exact congrArg (fun X : CompletedBoundaryHilbertSource =>
          completedBoundaryHilbertPairing T.source X) hD
      _ = 0 := by
        exact completedBoundaryHilbertPairing_zero_right T.source

/-- The concrete diagonal-debt cancellation stream is lower-weight null. -/
theorem completedBoundaryLowerWeightExactHilbertWeightStream_isLowerWeightNull_unconditional
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightNull
      (completedBoundaryLowerWeightExactHilbertWeightStream f) := by
  exact completedBoundaryHilbertWeightStream_isLowerWeightNull_of_source_eq_zero
    (completedBoundaryLowerWeightExactHilbertWeightStream f)
    (completedBoundaryLowerWeightExactSourceProbe f).source_eq_zero


/-- The completed boundary pairing is induced by the two-variable completed boundary kernel. -/
def completedBoundaryPairing
    (S T : CompletedBoundaryWeightStream) : ℝ :=
  Complex.re (completedBoundaryChannel (convolutionPair S.source T.source))

/-- The completed boundary pairing unfolds to the real part of the completed Hermitian
kernel. -/
theorem completedBoundaryPairing_eq_kernel
    (S T : CompletedBoundaryWeightStream) :
    completedBoundaryPairing S T =
      Complex.re (completedHermitianKernel S.source T.source) := by
  unfold completedBoundaryPairing
  exact congrArg Complex.re
    (completedBoundaryChannel_convolutionPair_eq_kernel S.source T.source)

/-- The diagonal of the completed boundary pairing is the completed boundary channel on the
convolution autocorrelation probe. -/
theorem completedBoundaryPairing_self_eq_boundaryChannel_autocorrelation
    (S : CompletedBoundaryWeightStream) :
    completedBoundaryPairing S S =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation S.source)) := by
  unfold completedBoundaryPairing
  exact congrArg
    (fun g : ZetaAdmissibleFunction =>
      Complex.re (completedBoundaryChannel g))
    (convolutionPair_self S.source)

/-- The scalar of a completed boundary weight stream is the self-pairing of its completed
boundary kernel. -/
theorem completedBoundaryWeightStream_scalar_eq_pairing_self
    (S : CompletedBoundaryWeightStream) :
    S.scalar = completedBoundaryPairing S S := by
  exact S.scalar_eq_completedBoundaryChannel.trans
    (completedBoundaryPairing_self_eq_boundaryChannel_autocorrelation S).symm

namespace CompletedBoundaryWeightStream

/-- A completed boundary weight stream is lower-weight null when it lies in the radical of
the completed boundary pairing. -/
def IsLowerWeightNull
    (D : CompletedBoundaryWeightStream) : Prop :=
  ∀ T : CompletedBoundaryWeightStream,
    completedBoundaryPairing D T = 0 ∧
      completedBoundaryPairing T D = 0

/-- A completed boundary weight stream is lower-weight exact when its completed diagonal
realization is zero.  This is the diagonal form of lower-weight absorption; positive
semidefiniteness of the completed pairing upgrades it to radical/nullity. -/
def IsLowerWeightExact
    (D : CompletedBoundaryWeightStream) : Prop :=
  D.scalar = 0

/-- A lower-weight null stream pairs trivially on the left. -/
theorem IsLowerWeightNull.pairing_left_eq_zero
    {D T : CompletedBoundaryWeightStream}
    (hD : IsLowerWeightNull D) :
    completedBoundaryPairing D T = 0 :=
  (hD T).1

/-- A lower-weight null stream pairs trivially on the right. -/
theorem IsLowerWeightNull.pairing_right_eq_zero
    {D T : CompletedBoundaryWeightStream}
    (hD : IsLowerWeightNull D) :
    completedBoundaryPairing T D = 0 :=
  (hD T).2

/-- A lower-weight null stream has zero self-pairing. -/
theorem IsLowerWeightNull.pairing_self_eq_zero
    {D : CompletedBoundaryWeightStream}
    (hD : IsLowerWeightNull D) :
    completedBoundaryPairing D D = 0 :=
  (hD D).1

/-- A lower-weight exact stream has zero completed self-pairing. -/
theorem IsLowerWeightExact.pairing_self_eq_zero
    {D : CompletedBoundaryWeightStream}
    (hD : IsLowerWeightExact D) :
    completedBoundaryPairing D D = 0 := by
  exact (completedBoundaryWeightStream_scalar_eq_pairing_self D).symm.trans hD

end CompletedBoundaryWeightStream

/-- Diagonal nullity implies left radicality for the completed Hilbert pairing. -/
theorem completedBoundaryHilbertPairing_left_zero_of_self_zero
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_smul_left :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing (a • x) y =
          a * completedBoundaryHilbertPairing x y)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (B_smul_right :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing x (a • y) =
          a * completedBoundaryHilbertPairing x y)
    (B_symm :
      ∀ x y : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x y =
          completedBoundaryHilbertPairing y x)
    (B_psd :
      ∀ x : CompletedBoundaryHilbertSource,
        0 ≤ completedBoundaryHilbertPairing x x)
    (D T : CompletedBoundaryHilbertWeightStream)
    (hDD : completedBoundaryHilbertPairing D.source D.source = 0) :
    completedBoundaryHilbertPairing D.source T.source = 0 := by
  exact
    real_symmetric_bilinear_psd_left_radical_of_self_zero
      completedBoundaryHilbertPairing
      B_add_left
      B_smul_left
      B_add_right
      B_smul_right
      B_symm
      B_psd
      (d := D.source)
      (t := T.source)
      hDD

/-- Diagonal nullity implies right radicality for the completed Hilbert pairing. -/
theorem completedBoundaryHilbertPairing_right_zero_of_self_zero
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_smul_left :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing (a • x) y =
          a * completedBoundaryHilbertPairing x y)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (B_smul_right :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing x (a • y) =
          a * completedBoundaryHilbertPairing x y)
    (B_symm :
      ∀ x y : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x y =
          completedBoundaryHilbertPairing y x)
    (B_psd :
      ∀ x : CompletedBoundaryHilbertSource,
        0 ≤ completedBoundaryHilbertPairing x x)
    (D T : CompletedBoundaryHilbertWeightStream)
    (hDD : completedBoundaryHilbertPairing D.source D.source = 0) :
    completedBoundaryHilbertPairing T.source D.source = 0 := by
  exact
    real_symmetric_bilinear_psd_right_radical_of_self_zero
      completedBoundaryHilbertPairing
      B_add_left
      B_smul_left
      B_add_right
      B_smul_right
      B_symm
      B_psd
      (d := D.source)
      (t := T.source)
      hDD

/-- Diagonal nullity of a Hilbert stream implies lower-weight nullity once the completed
Hilbert pairing has its symmetric bilinear positive-semidefinite laws. -/
theorem completedBoundaryHilbertWeightStream_isLowerWeightNull_of_self_pairing_zero
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_smul_left :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing (a • x) y =
          a * completedBoundaryHilbertPairing x y)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (B_smul_right :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing x (a • y) =
          a * completedBoundaryHilbertPairing x y)
    (B_symm :
      ∀ x y : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x y =
          completedBoundaryHilbertPairing y x)
    (B_psd :
      ∀ x : CompletedBoundaryHilbertSource,
        0 ≤ completedBoundaryHilbertPairing x x)
    (D : CompletedBoundaryHilbertWeightStream)
    (hDD : completedBoundaryHilbertPairing D.source D.source = 0) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightNull D := by
  intro T
  exact
    ⟨completedBoundaryHilbertPairing_left_zero_of_self_zero
        B_add_left B_smul_left B_add_right B_smul_right B_symm B_psd D T hDD,
      completedBoundaryHilbertPairing_right_zero_of_self_zero
        B_add_left B_smul_left B_add_right B_smul_right B_symm B_psd D T hDD⟩

/-- Lower-weight exact Hilbert streams lie in the radical/nullspace once the completed Hilbert
pairing has its symmetric bilinear positive-semidefinite laws. -/
theorem completedBoundaryHilbertWeightStream_isLowerWeightNull_of_lowerWeightExact
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_smul_left :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing (a • x) y =
          a * completedBoundaryHilbertPairing x y)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (B_smul_right :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing x (a • y) =
          a * completedBoundaryHilbertPairing x y)
    (B_symm :
      ∀ x y : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x y =
          completedBoundaryHilbertPairing y x)
    (B_psd :
      ∀ x : CompletedBoundaryHilbertSource,
        0 ≤ completedBoundaryHilbertPairing x x)
    (D : CompletedBoundaryHilbertWeightStream)
    (hD : CompletedBoundaryHilbertWeightStream.IsLowerWeightExact D) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightNull D := by
  exact completedBoundaryHilbertWeightStream_isLowerWeightNull_of_self_pairing_zero
    B_add_left
    B_smul_left
    B_add_right
    B_smul_right
    B_symm
    B_psd
    D
    (CompletedBoundaryHilbertWeightStream.IsLowerWeightExact.pairing_self_eq_zero hD)

/-- The concrete diagonal-debt cancellation stream is lower-weight null. -/
theorem completedBoundaryLowerWeightExactHilbertWeightStream_isLowerWeightNull
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightNull
      (completedBoundaryLowerWeightExactHilbertWeightStream f) := by
  exact completedBoundaryLowerWeightExactHilbertWeightStream_isLowerWeightNull_unconditional f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
