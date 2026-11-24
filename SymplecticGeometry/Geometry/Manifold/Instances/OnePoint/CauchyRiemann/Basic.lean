/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars

/-!
# Scratch
-/

public section

open Bundle Set TauCeti TauCeti.Manifold
open OnePoint (twistCore twistTransition)
open scoped Manifold ContDiff Topology TauCeti.ComplexManifold VectorBundle.ComplexToReal

noncomputable section

namespace OnePoint

instance (k : ℤ) (x : OnePoint ℂ) : ContinuousSMul ℝ ((twistCore (𝕜 := ℂ) k).Fiber x) :=
  inferInstanceAs (ContinuousSMul ℝ ℂ)

/-- `𝒪(k)` on the Riemann sphere is a `C^n` real vector bundle over the underlying real
surface, for every `n`. -/
instance (k : ℤ) {n : ℕ∞ω} : ContMDiffVectorBundle n ℂ (twistCore (𝕜 := ℂ) k).Fiber 𝓘(ℝ, ℂ) :=
  have : ContMDiffVectorBundle n ℂ (twistCore (𝕜 := ℂ) k).Fiber 𝓘(ℂ, ℂ) :=
    ContMDiffVectorBundle.of_le le_top
  ContMDiffVectorBundle.restrictScalars_modelWithCornersSelf ℝ this

end OnePoint

namespace SymplecticGeometry

variable {k : ℤ}

local instance (k : ℤ) (y : OnePoint ℂ) :
    MemTrivializationAtlas ((twistCore (𝕜 := ℂ) k).localTriv y) := ⟨⟨y, rfl⟩⟩

theorem twistCore_localTriv_symmL_apply {y x : OnePoint ℂ} (hx : x ∈ (chartAt ℂ y).source)
    (v : ℂ) :
    ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x v = twistTransition k y x x * v := by
  have hb : x ∈ ((twistCore (𝕜 := ℂ) k).localTriv y).baseSet := by simpa using hx
  rw [Trivialization.symmL_apply _ hb]
  have h := (twistCore (𝕜 := ℂ) k).localTriv_symm_apply y hb v
  rwa [OnePoint.twistCore_indexAt, OnePoint.twistCore_coordChange_apply] at h

theorem frameCovariantDerivative_twistCore {y x : OnePoint ℂ}
    (hx : x ∈ (chartAt ℂ y).source) {s : OnePoint ℂ → ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (s p)) x) :
    frameCovariantDerivative 𝓘(ℝ, ℂ) Complex.basisOneI ((twistCore k).localTriv y) s x =
      (((twistCore k).localTriv y).symmL ℝ x).comp
        (mvfderiv 𝓘(ℝ, ℂ) (fun p ↦ twistTransition k p y p * s p) x) := by
  have hg := ((twistCore (𝕜 := ℂ) k).localTriv y).mdifferentiableAt_section_iff 𝓘(ℝ, ℂ) s
    (by simpa using hx) |>.1 hs
  simp only [OnePoint.twistCore_localTriv_apply] at hg
  have hA : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun p ↦ twistTransition k p y p * s p) x
      (mvfderiv 𝓘(ℝ, ℂ) (fun p ↦ twistTransition k p y p * s p) x) := hg.hasMFDerivAt
  refine frameCovariantDerivative_eq_symmL_comp Complex.basisOneI hA (fun i ↦ ?_)
    (by simpa using hx)
  filter_upwards [((chartAt ℂ y).open_source.mem_nhds hx)] with z hz
  have h := ((twistCore (𝕜 := ℂ) k).localTriv y).localFrameCoeff_eq_coeff (I := 𝓘(ℝ, ℂ))
    (b := Complex.basisOneI) (s := (s : Π p, (twistCore (𝕜 := ℂ) k).Fiber p)) (i := i)
    (by simpa using hz)
  rw [Module.Basis.coord_apply]
  rwa [OnePoint.twistCore_localTriv_apply] at h

local notation "𝒊" => SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)

theorem zeroOnePart_frameCovariantDerivative_twistCore {y x : OnePoint ℂ}
    (hx : x ∈ (chartAt ℂ y).source) {s : OnePoint ℂ → ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (s p)) x) :
    𝒊.zeroOnePart
        (frameCovariantDerivative 𝓘(ℝ, ℂ) Complex.basisOneI ((twistCore k).localTriv y) s x) =
      (((twistCore k).localTriv y).symmL ℝ x).comp
        (𝒊.dbarFunction (fun p ↦ twistTransition k p y p * s p) x) := by
  rw [frameCovariantDerivative_twistCore hx hs]
  ext v
  simp only [SmoothAlmostComplexStructure.zeroOnePart_apply,
    SmoothAlmostComplexStructure.dbarFunction_apply, ContinuousLinearMap.comp_apply, map_add,
    map_smul]
  have (w : ℂ) : ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x (Complex.I • w) =
      Complex.I • ((twistCore (𝕜 := ℂ) k).localTriv y).symmL ℝ x w := by
    have hb : x ∈ ((twistCore (𝕜 := ℂ) k).localTriv y).baseSet := by simpa using hx
    rw [Trivialization.symmL_apply _ hb, Trivialization.symmL_apply _ hb,
      ← Trivialization.symmL_apply (R := ℂ) _ hb, ← Trivialization.symmL_apply (R := ℂ) _ hb,
      map_smul]
  rw [this]

theorem symmL_comp_dbarFunction_twistCore_eq {y y' x : OnePoint ℂ}
    (hx : x ∈ (chartAt ℂ y).source) (hx' : x ∈ (chartAt ℂ y').source) {s : OnePoint ℂ → ℂ}
    (hs : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ))
      (fun p ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) k).Fiber) p (s p)) x) :
    (((twistCore k).localTriv y).symmL ℝ x).comp
        (𝒊.dbarFunction (fun p ↦ twistTransition k p y p * s p) x) =
      (((twistCore k).localTriv y').symmL ℝ x).comp
        (𝒊.dbarFunction (fun p ↦ twistTransition k p y' p * s p) x) := by
  have hg := ((twistCore (𝕜 := ℂ) k).localTriv y).mdifferentiableAt_section_iff 𝓘(ℝ, ℂ) s
    (by simpa using hx) |>.1 hs
  simp only [OnePoint.twistCore_localTriv_apply] at hg
  have hU : (chartAt ℂ y).source ∩ (chartAt ℂ y').source ∈ 𝓝 x :=
    ((chartAt ℂ y).open_source.inter (chartAt ℂ y').open_source).mem_nhds ⟨hx, hx'⟩
  have ht : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (twistTransition k y y') x :=
    ((OnePoint.contMDiffOn_twistTransition k y y').contMDiffAt hU).mdifferentiableAt
      (by simp)
  have hcoord : (fun p ↦ twistTransition k p y' p * s p) =ᶠ[𝓝 x]
      twistTransition k y y' • fun p ↦ twistTransition k p y p * s p := by
    filter_upwards [hU] with p hp
    rw [Pi.smul_apply', smul_eq_mul, ← mul_assoc, OnePoint.twistTransition_mul_twistTransition k
      (mem_chart_source ℂ p) hp.1 hp.2]
  have hdbar : 𝒊.dbarFunction (fun p ↦ twistTransition k p y' p * s p) x =
      twistTransition k y y' x • 𝒊.dbarFunction (fun p ↦ twistTransition k p y p * s p) x := by
    rw [SmoothAlmostComplexStructure.dbarFunction_eq_zeroOnePart, hcoord.mvfderiv_eq,
      ← SmoothAlmostComplexStructure.dbarFunction_eq_zeroOnePart,
      SmoothAlmostComplexStructure.dbarFunction_smul _ (MDifferentiableAt.restrictScalars ℝ ht) hg,
      (SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_eq_zero_iff
        (MDifferentiableAt.restrictScalars ℝ ht)).2 ht]
    simp
  rw [hdbar]
  ext v
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply]
  rw [twistCore_localTriv_symmL_apply hx, twistCore_localTriv_symmL_apply hx', smul_eq_mul,
    ← mul_assoc, OnePoint.twistTransition_mul_twistTransition k hx hx' (mem_chart_source ℂ x)]


/-! ### The connection -/

/-- A smooth partition of unity on the sphere subordinate to the domains of its two charts. -/
def twistPartition : SmoothPartitionOfUnity (OnePoint ℂ) 𝓘(ℝ, ℂ) (OnePoint ℂ) univ :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, ℂ) (OnePoint ℂ)).choose

theorem twistPartition_isSubordinate :
    twistPartition.IsSubordinate fun y : OnePoint ℂ ↦ (chartAt ℂ y).source :=
  (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, ℂ) (OnePoint ℂ)).choose_spec

/-- The connection on `𝒪(1)` glued from the flat connections of the affine and of the inverted
frame by a partition of unity subordinate to the two charts. -/
def twistOneConnection (s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x) (x : OnePoint ℂ) :
    TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] (twistCore (𝕜 := ℂ) 1).Fiber x :=
  ∑ᶠ y, twistPartition y x •
    frameCovariantDerivative 𝓘(ℝ, ℂ) Complex.basisOneI ((twistCore 1).localTriv y) s x

theorem twistOneConnection_def (s : Π x, (twistCore (𝕜 := ℂ) 1).Fiber x) (x : OnePoint ℂ) :
    twistOneConnection s x = ∑ᶠ y, twistPartition y x •
      frameCovariantDerivative 𝓘(ℝ, ℂ) Complex.basisOneI ((twistCore 1).localTriv y) s x :=
  (rfl)

/-- The connection on `𝒪(1)` is a covariant derivative. -/
theorem isCovariantDerivativeOn_twistOneConnection :
    IsCovariantDerivativeOn ℂ twistOneConnection univ :=
  twistPartition_isSubordinate.toPartitionOfUnity.isCovariantDerivativeOn_finsum_smul
    fun y ↦ by
      rw [← OnePoint.twistCore_localTriv_baseSet 1 y]
      exact isCovariantDerivativeOn_frameCovariantDerivative Complex.basisOneI

/-- The connection on `𝒪(1)` is smooth: it sends `C^(n + 1)` sections to `C^n` one-forms. -/
theorem contMDiffCovariantDerivativeOn_twistOneConnection (n : ℕ∞) :
    ContMDiffCovariantDerivativeOn ℂ n twistOneConnection univ :=
  twistPartition_isSubordinate.contMDiffCovariantDerivativeOn_finsum_smul
    (fun y ↦ (chartAt ℂ y).open_source) fun y ↦ by
      rw [← OnePoint.twistCore_localTriv_baseSet 1 y]
      exact contMDiffCovariantDerivativeOn_frameCovariantDerivative (m := ω) (k := ω)
        Complex.basisOneI le_top le_top

end SymplecticGeometry
