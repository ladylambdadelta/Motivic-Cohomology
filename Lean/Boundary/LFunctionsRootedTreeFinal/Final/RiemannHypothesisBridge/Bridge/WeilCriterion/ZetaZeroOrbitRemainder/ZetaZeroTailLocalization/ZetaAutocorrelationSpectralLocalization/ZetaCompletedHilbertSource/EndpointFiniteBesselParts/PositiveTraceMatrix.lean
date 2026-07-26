import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompression
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.Owner
import Mathlib.Topology.Order.OrderClosed

/-!
# Endpoint finite positive trace matrix

This file owns the finite endpoint objects and the algebraic Schur-complement
API for the positive trace matrix.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The finite positive trace matrix seen by the endpoint compression. -/
structure CompletedEndpointFinitePositiveTraceMatrix where
  traceScalar : ℝ
  endpointCompressionScalar : ℝ
  hiddenKernelScalar : ℝ

namespace CompletedEndpointFinitePositiveTraceMatrix

/-- Schur-complement positivity for a finite positive trace matrix. -/
def SchurCompression
    (M : CompletedEndpointFinitePositiveTraceMatrix) : Prop :=
  0 ≤ M.hiddenKernelScalar

/-- A positive finite trace matrix splits into its visible endpoint compression
and a nonnegative hidden kernel. -/
def KernelSplit
    (M : CompletedEndpointFinitePositiveTraceMatrix) : Prop :=
  ∃ hiddenKernel : ℝ,
    M.traceScalar = M.endpointCompressionScalar + hiddenKernel ∧
    0 ≤ hiddenKernel ∧
    M.hiddenKernelScalar = hiddenKernel

end CompletedEndpointFinitePositiveTraceMatrix

/-- The concrete finite positive trace matrix attached to a cutoff and seed. -/
noncomputable def completedEndpointFinitePositiveTraceMatrix
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    CompletedEndpointFinitePositiveTraceMatrix :=
  { traceScalar := finitePositiveRenormalizedBoundaryWindow N f
    endpointCompressionScalar := (completedWeilEndpointTraceFiber f).gram
    hiddenKernelScalar :=
      finitePositiveRenormalizedBoundaryWindow N f -
        (completedWeilEndpointTraceFiber f).gram }

/-- The concrete finite trace matrix trace scalar is the finite renormalized
boundary window. -/
theorem completedEndpointFinitePositiveTraceMatrix_traceScalar_eq
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedEndpointFinitePositiveTraceMatrix N f).traceScalar =
      finitePositiveRenormalizedBoundaryWindow N f :=
  Eq.refl (finitePositiveRenormalizedBoundaryWindow N f)

/-- The concrete finite trace matrix endpoint compression scalar is the
endpoint trace Gram. -/
theorem completedEndpointFinitePositiveTraceMatrix_endpointCompressionScalar_eq
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar =
      (completedWeilEndpointTraceFiber f).gram :=
  Eq.refl ((completedWeilEndpointTraceFiber f).gram)

/-- The concrete finite trace matrix hidden-kernel scalar is trace minus
endpoint compression. -/
theorem completedEndpointFinitePositiveTraceMatrix_hiddenKernelScalar_eq
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar =
      finitePositiveRenormalizedBoundaryWindow N f -
        (completedWeilEndpointTraceFiber f).gram :=
  Eq.refl
    (finitePositiveRenormalizedBoundaryWindow N f -
      (completedWeilEndpointTraceFiber f).gram)

/-- The finite hidden endpoint kernel window is the renormalized finite
boundary window after removing the completed visible endpoint trace Gram. -/
noncomputable def completedEndpointPhysicalHiddenKernelWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePositiveRenormalizedBoundaryWindow N f -
    (completedWeilEndpointTraceFiber f).gram

/-- The finite hidden endpoint kernel window unfolds to the renormalized
boundary window minus the endpoint trace Gram. -/
theorem completedEndpointPhysicalHiddenKernelWindow_eq_renormalizedBoundaryWindow_sub_endpointFiberGram
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedEndpointPhysicalHiddenKernelWindow N f =
      finitePositiveRenormalizedBoundaryWindow N f -
        (completedWeilEndpointTraceFiber f).gram :=
  Eq.refl
    (finitePositiveRenormalizedBoundaryWindow N f -
      (completedWeilEndpointTraceFiber f).gram)

/-- The finite endpoint Bessel compression statement for one cutoff. -/
def CompletedEndpointFiniteBesselCompression
    (N : ℕ) (f : ZetaAdmissibleFunction) : Prop :=
  (completedWeilEndpointTraceFiber f).gram ≤
    finitePositiveRenormalizedBoundaryWindow N f

/-- The finite endpoint Bessel Schur remainder at one cutoff. -/
noncomputable def completedEndpointFiniteBesselSchurRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePositiveRenormalizedBoundaryWindow N f -
    (completedWeilEndpointTraceFiber f).gram

/-- The finite endpoint Bessel Schur remainder is the hidden endpoint kernel
window. -/
theorem completedEndpointFiniteBesselSchurRemainder_eq_hiddenKernelWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedEndpointFiniteBesselSchurRemainder N f =
      completedEndpointPhysicalHiddenKernelWindow N f :=
  Eq.refl (completedEndpointFiniteBesselSchurRemainder N f)

/-- The finite endpoint Bessel Schur remainder is the hidden-kernel scalar of
the concrete finite positive trace matrix. -/
theorem completedEndpointFiniteBesselSchurRemainder_eq_positiveTraceMatrix_hiddenKernelScalar
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedEndpointFiniteBesselSchurRemainder N f =
      (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar :=
  Eq.refl (completedEndpointFiniteBesselSchurRemainder N f)

/-- The finite renormalized boundary window splits into the visible endpoint
trace Gram plus the finite Bessel Schur remainder. -/
theorem finitePositiveRenormalizedBoundaryWindow_eq_endpointTraceGram_add_finiteBesselSchurRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePositiveRenormalizedBoundaryWindow N f =
      (completedWeilEndpointTraceFiber f).gram +
        completedEndpointFiniteBesselSchurRemainder N f :=
  let boundary : ℝ := finitePositiveRenormalizedBoundaryWindow N f
  let endpointGram : ℝ := (completedWeilEndpointTraceFiber f).gram
  endpointTraceDebt_add_sub_cancel boundary endpointGram

/-- The concrete finite positive trace matrix has the expected algebraic
trace/endpoints/hidden-kernel split once its hidden kernel is known
nonnegative. -/
theorem completedEndpointFinitePositiveTraceMatrix_kernelSplit_of_hiddenKernel_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hhidden :
      0 ≤ (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar) :
    CompletedEndpointFinitePositiveTraceMatrix.KernelSplit
      (completedEndpointFinitePositiveTraceMatrix N f) :=
  let M : CompletedEndpointFinitePositiveTraceMatrix :=
    completedEndpointFinitePositiveTraceMatrix N f
  let hiddenKernel : ℝ := M.hiddenKernelScalar
  let htrace :
      M.traceScalar = M.endpointCompressionScalar + hiddenKernel :=
    finitePositiveRenormalizedBoundaryWindow_eq_endpointTraceGram_add_finiteBesselSchurRemainder
      N f
  let hhiddenNamed : 0 ≤ hiddenKernel := hhidden
  let hhiddenEq : M.hiddenKernelScalar = hiddenKernel := Eq.refl hiddenKernel
  Exists.intro hiddenKernel
    (And.intro htrace
      (And.intro hhiddenNamed hhiddenEq))

/-- A finite positive trace-matrix kernel split gives hidden-kernel
nonnegativity. -/
theorem completedEndpointFinitePositiveTraceMatrix_hiddenKernel_nonnegative_of_kernelSplit
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hsplit :
      CompletedEndpointFinitePositiveTraceMatrix.KernelSplit
        (completedEndpointFinitePositiveTraceMatrix N f)) :
    0 ≤ (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar :=
  match hsplit with
  | ⟨hiddenKernel, htrace, hnonnegative, hhiddenEq⟩ =>
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hhiddenEq.symm
        hnonnegative

/-- Finite endpoint trace-compression exhaustion. -/
def CompletedEndpointFiniteTraceCompressionExhaustion
    (f : ZetaAdmissibleFunction) : Prop :=
  ∀ᶠ N in atTop, CompletedEndpointFiniteBesselCompression N f

/-- Eventual nonnegativity of the finite endpoint Schur complements. -/
def CompletedEndpointFiniteSchurComplementExhaustion
    (f : ZetaAdmissibleFunction) : Prop :=
  ∀ᶠ N in atTop, 0 ≤ completedEndpointFiniteBesselSchurRemainder N f

/-- Finite positive trace-matrix endpoint Schur compression. -/
def CompletedEndpointFinitePositiveTraceMatrixSchurCompression
    (N : ℕ) (f : ZetaAdmissibleFunction) : Prop :=
  CompletedEndpointFinitePositiveTraceMatrix.SchurCompression
    (completedEndpointFinitePositiveTraceMatrix N f)

/-- Finite endpoint-vector Bessel domination inside the positive trace
matrix. -/
def CompletedEndpointFinitePositiveTraceMatrixEndpointBesselDomination
    (N : ℕ) (f : ZetaAdmissibleFunction) : Prop :=
  (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar ≤
    (completedEndpointFinitePositiveTraceMatrix N f).traceScalar

/-- The finite endpoint vector is realized as a vector in the positive finite
trace model.  This is the finite GNS ownership statement behind endpoint
Bessel domination. -/
def CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
    (N : ℕ) (f : ZetaAdmissibleFunction) : Prop :=
  ∃ hiddenKernel : ℝ,
    (completedEndpointFinitePositiveTraceMatrix N f).traceScalar =
      (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar +
        hiddenKernel ∧
    0 ≤ hiddenKernel

/-- A finite positive trace frame realizing the endpoint vector. -/
structure CompletedEndpointFinitePositiveTraceFrame
    (N : ℕ) (f : ZetaAdmissibleFunction) where
  ambientNormSq : ℝ
  endpointVectorNormSq : ℝ
  complementNormSq : ℝ
  ambient_eq_trace :
    ambientNormSq =
      (completedEndpointFinitePositiveTraceMatrix N f).traceScalar
  endpoint_eq_compression :
    endpointVectorNormSq =
      (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar
  ambient_split :
    ambientNormSq = endpointVectorNormSq + complementNormSq
  complement_nonnegative :
    0 ≤ complementNormSq

/-- The canonical finite trace-frame complement norm-square. -/
noncomputable def completedEndpointFinitePositiveTraceFrameComplementNormSq
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  (completedEndpointFinitePositiveTraceMatrix N f).traceScalar -
    (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar

/-- The canonical finite trace-frame complement norm-square is the hidden
kernel scalar of the finite positive trace matrix. -/
theorem completedEndpointFinitePositiveTraceFrameComplementNormSq_eq_hiddenKernelScalar
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedEndpointFinitePositiveTraceFrameComplementNormSq N f =
      (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar :=
  Eq.refl (completedEndpointFinitePositiveTraceFrameComplementNormSq N f)

/-- A nonnegative canonical complement norm-square constructs the finite
positive trace frame. -/
noncomputable def completedEndpointFinitePositiveTraceFrame_of_complementNormSq_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hcomplement :
      0 ≤ completedEndpointFinitePositiveTraceFrameComplementNormSq N f) :
    CompletedEndpointFinitePositiveTraceFrame N f :=
  { ambientNormSq := (completedEndpointFinitePositiveTraceMatrix N f).traceScalar
    endpointVectorNormSq :=
      (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar
    complementNormSq :=
      completedEndpointFinitePositiveTraceFrameComplementNormSq N f
    ambient_eq_trace :=
      Eq.refl ((completedEndpointFinitePositiveTraceMatrix N f).traceScalar)
    endpoint_eq_compression :=
      Eq.refl
        ((completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar)
    ambient_split :=
      endpointTraceDebt_add_sub_cancel
        (completedEndpointFinitePositiveTraceMatrix N f).traceScalar
        (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar
    complement_nonnegative := hcomplement }

/-- A finite positive trace frame gives an endpoint-vector realization in the
finite positive trace matrix. -/
theorem completedEndpointFinitePositiveTraceMatrixEndpointVectorRealization_of_traceFrame
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (frame : CompletedEndpointFinitePositiveTraceFrame N f) :
    CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization
      N f :=
  let hiddenKernel : ℝ := frame.complementNormSq
  let htraceEndpoint :
      (completedEndpointFinitePositiveTraceMatrix N f).traceScalar =
        (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar +
          hiddenKernel :=
    let htrace :
        (completedEndpointFinitePositiveTraceMatrix N f).traceScalar =
          frame.ambientNormSq :=
      frame.ambient_eq_trace.symm
    let hsplit :
        frame.ambientNormSq =
          frame.endpointVectorNormSq + hiddenKernel :=
      frame.ambient_split
    let hendpoint :
        frame.endpointVectorNormSq =
          (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar :=
      frame.endpoint_eq_compression
    htrace.trans
      (hsplit.trans
        (congrArg
          (fun value : ℝ => value + hiddenKernel)
          hendpoint))
  let hhidden : 0 ≤ hiddenKernel := frame.complement_nonnegative
  Exists.intro hiddenKernel
    (And.intro htraceEndpoint hhidden)

/-- A finite positive trace frame gives hidden-kernel nonnegativity in the
finite positive trace matrix. -/
theorem completedEndpointFinitePositiveTraceMatrix_hiddenKernel_nonnegative_of_traceFrame
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (frame : CompletedEndpointFinitePositiveTraceFrame N f) :
    0 ≤ (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar :=
  let M : CompletedEndpointFinitePositiveTraceMatrix :=
    completedEndpointFinitePositiveTraceMatrix N f
  let complement : ℝ := frame.complementNormSq
  let htrace :
      M.traceScalar = M.endpointCompressionScalar + complement :=
    let htraceFrame :
        (completedEndpointFinitePositiveTraceMatrix N f).traceScalar =
          frame.ambientNormSq :=
      frame.ambient_eq_trace.symm
    let hsplit :
        frame.ambientNormSq =
          frame.endpointVectorNormSq + frame.complementNormSq :=
      frame.ambient_split
    let hendpoint :
        frame.endpointVectorNormSq =
          (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar :=
      frame.endpoint_eq_compression
    htraceFrame.trans
      (hsplit.trans
        (congrArg
          (fun value : ℝ => value + frame.complementNormSq)
          hendpoint))
  let hsub :
      M.traceScalar - M.endpointCompressionScalar = complement :=
    let hcalc :
        M.endpointCompressionScalar + complement - M.endpointCompressionScalar =
          complement :=
      add_sub_cancel_left M.endpointCompressionScalar complement
    (congrArg
      (fun value : ℝ => value - M.endpointCompressionScalar)
      htrace).trans hcalc
  let hhidden :
      M.hiddenKernelScalar = M.traceScalar - M.endpointCompressionScalar :=
    Eq.refl M.hiddenKernelScalar
  let hcomplement : 0 ≤ complement := frame.complement_nonnegative
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (hhidden.trans hsub).symm
    hcomplement

/-- A finite endpoint-vector realization gives endpoint Bessel domination in
the finite positive trace matrix. -/
theorem completedEndpointFinitePositiveTraceMatrixEndpointBesselDomination_of_endpointVectorRealization
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hrealization :
      CompletedEndpointFinitePositiveTraceMatrixEndpointVectorRealization N f) :
    CompletedEndpointFinitePositiveTraceMatrixEndpointBesselDomination
      N f :=
  match hrealization with
  | ⟨hiddenKernel, htrace, hnonnegative⟩ =>
      have hle :
          (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar ≤
            (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar +
              hiddenKernel :=
        le_add_of_nonneg_right hnonnegative
      Eq.subst
        (motive := fun value : ℝ =>
          (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar ≤
            value)
        htrace.symm
        hle

/-- Finite positive trace-matrix endpoint Bessel domination unfolds to finite
endpoint Bessel compression. -/
theorem completedEndpointFiniteBesselCompression_of_positiveTraceMatrixEndpointBesselDomination
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hdomination :
      CompletedEndpointFinitePositiveTraceMatrixEndpointBesselDomination
        N f) :
    CompletedEndpointFiniteBesselCompression N f :=
  let hendpoint :
      (completedEndpointFinitePositiveTraceMatrix N f).endpointCompressionScalar =
        (completedWeilEndpointTraceFiber f).gram :=
    completedEndpointFinitePositiveTraceMatrix_endpointCompressionScalar_eq N f
  let htrace :
      (completedEndpointFinitePositiveTraceMatrix N f).traceScalar =
        finitePositiveRenormalizedBoundaryWindow N f :=
    completedEndpointFinitePositiveTraceMatrix_traceScalar_eq N f
  let hseedTrace :
      (completedWeilEndpointTraceFiber f).gram ≤
        (completedEndpointFinitePositiveTraceMatrix N f).traceScalar :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ (completedEndpointFinitePositiveTraceMatrix N f).traceScalar)
      hendpoint
      hdomination
  Eq.subst
    (motive := fun value : ℝ =>
      (completedWeilEndpointTraceFiber f).gram ≤ value)
    htrace
    hseedTrace

/-- Endpoint-vector Bessel domination gives hidden-kernel nonnegativity. -/
theorem completedEndpointFinitePositiveTraceMatrix_hiddenKernel_nonnegative_of_endpointBesselDomination
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hdomination :
      CompletedEndpointFinitePositiveTraceMatrixEndpointBesselDomination
        N f) :
    0 ≤ (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar :=
  let M : CompletedEndpointFinitePositiveTraceMatrix :=
    completedEndpointFinitePositiveTraceMatrix N f
  let hsub :
      0 ≤ M.traceScalar - M.endpointCompressionScalar :=
    sub_nonneg.mpr hdomination
  let hhidden :
      M.hiddenKernelScalar = M.traceScalar - M.endpointCompressionScalar :=
    Eq.refl M.hiddenKernelScalar
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    hhidden.symm
    hsub

/-- Hidden-kernel nonnegativity of the concrete finite positive trace matrix
gives the public finite Schur-compression predicate. -/
theorem completedEndpointFinitePositiveTraceMatrixSchurCompression_of_hiddenKernel_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hhidden :
      0 ≤ (completedEndpointFinitePositiveTraceMatrix N f).hiddenKernelScalar) :
    CompletedEndpointFinitePositiveTraceMatrixSchurCompression N f :=
  hhidden

/-- The public finite Schur-compression predicate gives nonnegativity of the
finite Bessel Schur remainder. -/
theorem completedEndpointFiniteBesselSchurRemainder_nonnegative_of_positiveTraceMatrixSchurCompression
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hschur : CompletedEndpointFinitePositiveTraceMatrixSchurCompression N f) :
    0 ≤ completedEndpointFiniteBesselSchurRemainder N f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointFiniteBesselSchurRemainder_eq_positiveTraceMatrix_hiddenKernelScalar
      N f).symm
    hschur

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
