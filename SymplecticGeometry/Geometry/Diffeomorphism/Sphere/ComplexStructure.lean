/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Cayley.Path
public import Mathlib.Topology.Homotopy.Basic
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Topology
import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Contractible
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
import SymplecticGeometry.LinearAlgebra.Complex.Orientation

/-!
# Orientation-preserving diffeomorphisms of the sphere and tame complex structures

Let `S²` be the Riemann sphere `OnePoint ℂ`, seen as a real surface over the model `𝓘(ℝ, ℂ)`,
let `i` be the almost complex structure of the complex manifold `OnePoint ℂ`
(`TauCeti.SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)`), and let `ω_FS` be the
Fubini–Study form `OnePoint.fubiniStudyForm`, which is compatible with `i`
(`OnePoint.compatible_fubiniStudyForm`). The space `𝒥` of smooth almost complex structures on `S²`
tamed by `ω_FS` is the subtype `{J // OnePoint.fubiniStudyForm.Tames J}`; in this file `𝒥` is a
local notation for it.

* `SymplecticGeometry.diffPlus`: the subgroup `Diff⁺(S²)` of smooth diffeomorphisms of `S²` that
  preserve the orientation of the complex manifold at every point, Tau Ceti's
  `Diffeomorph.orientationPreservingSubgroup` for `TauCeti.complexManifoldOrientation`, with
  `SymplecticGeometry.mem_diffPlus_iff`.
* `SymplecticGeometry.tameOfComplexManifold`: the structure `i`, as an element of `𝒥`.
* `SymplecticGeometry.mem_diffPlus_iff_tames_pullback`: a diffeomorphism `φ` of `S²` lies in
  `Diff⁺(S²)` exactly when `ω_FS` tames the pulled-back structure `φ^* i`. At a point `x`, with
  `L` the derivative of `φ` at `x` read in the charts, `(φ^* i)_x = L⁻¹ ∘ i ∘ L` and
  `ω_FS(v, w)` is a positive multiple of `Im (conj v * w)`
  (`OnePoint.eval₂_fubiniStudyForm`). So both conditions say that `L` has positive
  determinant (`Complex.det_pos_iff_forall_im_conj_mul_symm_I_mul_pos` and
  `Diffeomorph.isOrientationPreservingAt_complexManifoldOrientation_iff_det_pos`).
* `SymplecticGeometry.complexStructureMap`: the map `Diff⁺(S²) → 𝒥`, `φ ↦ φ^* i`, with
  `SymplecticGeometry.coe_complexStructureMap`, `SymplecticGeometry.complexStructureMap_one` and
  `SymplecticGeometry.complexStructureMap_mul`: `(φ ψ)^* i = ψ^* (φ^* i)`, from
  `TauCeti.SmoothAlmostComplexStructure.pullback_mul`, a form of Tau Ceti's `pullback_trans`.
* `SymplecticGeometry.continuous_complexStructureMap`: for any frame system, `φ ↦ φ^* i` is
  continuous from the weak Whitney topology on `Diff⁺(S²)` (`TauCeti.DiffeomorphWeakWhitney`) to
  Tau Ceti's `C^∞` topology `TauCeti.SmoothAlmostComplexStructure.frameTopology` on `𝒥`; it is
  the case of the sphere of `TauCeti.SmoothAlmostComplexStructure.continuous_pullback`.
* `SymplecticGeometry.complexStructureContraction`: for any covering frame system, a homotopy
  relative to `{i}` from the identity of `𝒥` to the constant map at `i`, with
  `SymplecticGeometry.complexStructureContraction_apply`. At time `t` it sends `J` to the Cayley
  path from `i` to `J` at time `1 - t` (Tau Ceti's `TauCeti.SmoothTwoForm.Compatible.cayleyPath`
  for `OnePoint.compatible_fubiniStudyForm`): it is the case `J₀ = i` of
  `TauCeti.SmoothTwoForm.Compatible.cayleyContraction`. At each point of `S²` the Cayley path
  shrinks the disc of tame complex structures on the tangent plane radially onto its centre.

## References

* [C. J. Earle, J. Eells, *The diffeomorphism group of a compact Riemann
  surface*][EarleEells1967] (the action of orientation-preserving diffeomorphisms on complex
  structures).
* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 2, §1 (the weak topology on
  spaces of maps).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  p. 164 (on a surface, the almost complex structures tamed by an area form are those inducing
  its orientation).
-/

public section

open scoped Manifold ContDiff TauCeti.ComplexManifold TauCeti.DiffeomorphWeakWhitney
open TauCeti

namespace SymplecticGeometry

/-- The smooth almost complex structures on the Riemann sphere tamed by the Fubini–Study form. -/
local notation "𝒥" =>
  {J : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ) // OnePoint.fubiniStudyForm.Tames J}

/-- The group `Diff⁺(S²)` of smooth diffeomorphisms of the Riemann sphere, as a real surface,
that preserve the orientation of the complex manifold `OnePoint ℂ` at every point. -/
noncomputable def diffPlus : Subgroup (TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞) :=
  Diffeomorph.orientationPreservingSubgroup (by simp) (complexManifoldOrientation ℂ (OnePoint ℂ))

theorem diffPlus_def : diffPlus = Diffeomorph.orientationPreservingSubgroup (by simp)
    (complexManifoldOrientation ℂ (OnePoint ℂ)) :=
  (rfl)

/-- A diffeomorphism of the Riemann sphere lies in `diffPlus` exactly when it preserves the
orientation of the complex manifold `OnePoint ℂ` at every point. -/
theorem mem_diffPlus_iff {φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞} :
    φ ∈ diffPlus ↔ ∀ x, Manifold.Orientation.IsOrientationPreservingAt
      (complexManifoldOrientation ℂ (OnePoint ℂ)) (complexManifoldOrientation ℂ (OnePoint ℂ))
        φ x := by
  rw [diffPlus_def, Diffeomorph.mem_orientationPreservingSubgroup_iff]

/-- The almost complex structure of the complex manifold `OnePoint ℂ`, as a structure tamed by the
Fubini–Study form. -/
noncomputable def tameOfComplexManifold : 𝒥 :=
  ⟨SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ),
    OnePoint.compatible_fubiniStudyForm.tames⟩

@[simp]
theorem coe_tameOfComplexManifold :
    (tameOfComplexManifold : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)) =
      SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ) :=
  (rfl)

/-- A diffeomorphism `φ` of the Riemann sphere preserves the orientation of the complex manifold
at every point exactly when the Fubini–Study form tames the pull-back `φ^* i` of the complex
structure `i`. -/
theorem mem_diffPlus_iff_tames_pullback {φ : TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞} :
    φ ∈ diffPlus ↔ OnePoint.fubiniStudyForm.Tames
      ((SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).pullback φ) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  simp only [mem_diffPlus_iff, SmoothTwoForm.tames_iff, SmoothAlmostComplexStructure.pullback_apply,
    SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold,
    ← φ.mfderivToContinuousLinearEquiv_coe hn, ContinuousLinearMap.inverse_equiv,
    φ.isOrientationPreservingAt_complexManifoldOrientation_iff_det_pos hn]
  refine forall_congr' fun x ↦ (Complex.det_pos_iff_forall_im_conj_mul_symm_I_mul_pos
    (φ.mfderivToContinuousLinearEquiv hn x).toLinearEquiv).trans (forall₂_congr fun v _ ↦ ?_)
  -- The Fubini–Study form at `x` is a positive multiple of `(v, w) ↦ Im (conj v * w)`.
  exact (mul_pos_iff_of_pos_left (OnePoint.fubiniStudyDensity_pos _)).symm.trans
    (congrArg (0 < ·) (OnePoint.eval₂_fubiniStudyForm x v _)).symm.to_iff

/-- The map `Diff⁺(S²) → 𝒥` that sends `φ` to the pull-back `φ^* i` of the complex structure `i`
of the Riemann sphere. -/
noncomputable def complexStructureMap (φ : diffPlus) : 𝒥 :=
  ⟨(SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).pullback φ,
    mem_diffPlus_iff_tames_pullback.1 φ.property⟩

@[simp]
theorem coe_complexStructureMap (φ : diffPlus) :
    (complexStructureMap φ : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)) =
      (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)).pullback φ :=
  (rfl)

/-- The identity pulls `i` back to itself. -/
@[simp]
theorem complexStructureMap_one : complexStructureMap 1 = tameOfComplexManifold := by
  ext1
  rw [coe_complexStructureMap, Subgroup.coe_one, SmoothAlmostComplexStructure.pullback_one,
    coe_tameOfComplexManifold]

/-- Pulling `i` back along a product is the iterated pull-back: `(φ ψ)^* i = ψ^* (φ^* i)`. -/
theorem complexStructureMap_mul (φ ψ : diffPlus) :
    (complexStructureMap (φ * ψ) : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)) =
      (complexStructureMap φ : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)).pullback ψ := by
  rw [coe_complexStructureMap, coe_complexStructureMap, Subgroup.coe_mul,
    SmoothAlmostComplexStructure.pullback_mul]

/-- For any frame system of `End(TS²)`, the map `Diff⁺(S²) → 𝒥`, `φ ↦ φ^* i`, is continuous for
the weak Whitney topology on `Diff⁺(S²)` and the `C^∞` topology on `𝒥`. -/
theorem continuous_complexStructureMap {ι : Type*}
    (e : ι → Bundle.Trivialization (ℂ →L[ℝ] ℂ) (Bundle.TotalSpace.proj (F := ℂ →L[ℝ] ℂ)
      (E := fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x)))
    [∀ k, MemTrivializationAtlas (e k)] (U : ι → TopologicalSpace.Opens (OnePoint ℂ))
    (hU : ∀ k, (U k : Set (OnePoint ℂ)) ⊆ (e k).baseSet) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    Continuous complexStructureMap := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  exact ((SmoothAlmostComplexStructure.continuous_pullback e U hU _).comp
    continuous_subtypeVal).subtype_mk _

/-- For any covering frame system of `End(TS²)`, the space `𝒥` of structures tamed by the
Fubini–Study form contracts onto the structure `i` of the Riemann sphere, relative to `i`, for the
`C^∞` topology: at time `t` the homotopy sends `J` to the Cayley path from `i` to `J` at time
`1 - t`. -/
noncomputable def complexStructureContraction {ι : Type*}
    (e : ι → Bundle.Trivialization (ℂ →L[ℝ] ℂ) (Bundle.TotalSpace.proj (F := ℂ →L[ℝ] ℂ)
      (E := fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x)))
    [∀ k, MemTrivializationAtlas (e k)] (U : ι → TopologicalSpace.Opens (OnePoint ℂ))
    (hU : ∀ k, (U k : Set (OnePoint ℂ)) ⊆ (e k).baseSet) (hcover : ∀ x, ∃ k, x ∈ U k) :
    letI := SmoothAlmostComplexStructure.frameTopology e U hU
    (ContinuousMap.id 𝒥).HomotopyRel (ContinuousMap.const _ tameOfComplexManifold)
      {tameOfComplexManifold} :=
  OnePoint.compatible_fubiniStudyForm.cayleyContraction e U hU hcover

/-- At time `t`, the contraction of `𝒥` onto `i` sends `J` to the Cayley path from `i` to `J` at
time `1 - t`. -/
@[simp]
theorem complexStructureContraction_apply {ι : Type*}
    (e : ι → Bundle.Trivialization (ℂ →L[ℝ] ℂ) (Bundle.TotalSpace.proj (F := ℂ →L[ℝ] ℂ)
      (E := fun x : OnePoint ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x)))
    [∀ k, MemTrivializationAtlas (e k)] (U : ι → TopologicalSpace.Opens (OnePoint ℂ))
    (hU : ∀ k, (U k : Set (OnePoint ℂ)) ⊆ (e k).baseSet) (hcover : ∀ x, ∃ k, x ∈ U k)
    (t : unitInterval) (J : 𝒥) :
    (complexStructureContraction e U hU hcover (t, J) :
        SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) (OnePoint ℂ)) =
      OnePoint.compatible_fubiniStudyForm.cayleyPath J.property (1 - t) :=
  OnePoint.compatible_fubiniStudyForm.cayleyContraction_apply e U hU hcover t J

end SymplecticGeometry

end
