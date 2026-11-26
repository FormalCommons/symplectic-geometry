/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.ComplexStructure
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Prod
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Representative
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Pullback
public import TauCeti.Geometry.Symplectic.Manifold.Volume
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Dual
import SymplecticGeometry.Geometry.Symplectic.Manifold.Volume
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.Splitting
import SymplecticGeometry.Geometry.Manifold.SmoothEmbedding.NormalSpace.Representative
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Orthogonal
import TauCeti.Geometry.Manifold.VectorBundle.Prod
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity
import TauCeti.Geometry.Symplectic.Lagrangian.Basic

/-!
# The symplectic splitting of the tangent bundle along a `J`-invariant submanifold

Let `J` be a smooth almost complex structure on `X`, and `f : M → X` a smooth embedding whose
tangent images `W_x = df_x (T_x M)` are `J`-invariant. Write `Jf` for the pull-back of `J` to the
bundle `f *ᵖ TX` over `M` (`TauCeti.SmoothAlmostComplexStructure.pullbackComplexStructure`, in
`SymplecticGeometry/Geometry/Manifold/VectorBundle/ComplexStructure.lean`), and let `ω` be a
two-form on `f *ᵖ TX` that tames `Jf`. Then:

* `ω` is nondegenerate on each `W_x`, so `W_x` and its `ω`-orthogonal `W_x^ω` are complements,
  and `W_x^ω` is `Jf`-invariant when `ω` is `Jf`-invariant;
* `ω` read through `df` is a nondegenerate two-form `σ` on `TM`, positive on the pairs
  `(u, v)` with `df v = J (df u)`. This is `ω.compMFDeriv f f.contMDiff`
  (`SymplecticGeometry.Bundle.ContMDiffTwoForm.compMFDeriv`, defined for any smooth map in
  `SymplecticGeometry/Geometry/Manifold/VectorBundle/Symplectic/Pullback.lean`). When `M` is a
  surface, the symplectic orientation of `σ` is the orientation of `M` in which every frame
  `(u, v)` with `df v = J (df u)` is positive;
* `ω` read through the representatives in `W^ω` of the normal classes is a two-form `ω_ν` on the
  normal bundle `ν`, compatible with the complex structure that `J` induces on `ν` when `ω` is
  compatible with `Jf`;
* the fibrewise map `v ↦ ((df)⁻¹ P_W v, [v])`, with `P_W` the projection onto `W` along `W^ω`, is
  a smooth isomorphism from `f *ᵖ TX` to `TM ×ᵇ ν` carrying `ω` to `σ.prod ω_ν`.

So `(f *ᵖ TX, ω)` is the direct sum of the symplectic bundles `(TM, σ)` and `(ν, ω_ν)`. Over a
Hausdorff σ-compact `M`, a form compatible with `Jf` exists by
`SymplecticGeometry.Bundle.ContMDiffComplexStructure.exists_compatible`.

## Main definitions

* `TauCeti.SmoothEmbedding.normalForm`: the two-form `ω_ν` on the normal bundle.
* `TauCeti.SmoothEmbedding.normalSplitting`: the fibrewise isomorphism
  `f *ᵖ TX ≃ TM ×ᵇ ν`, the inverse of `TauCeti.SmoothEmbedding.tangentNormalEquiv`
  (`SymplecticGeometry/Geometry/Manifold/SmoothEmbedding/NormalSpace/Splitting.lean`) for the
  representatives in `W^ω`.

## Main results

* `TauCeti.SmoothEmbedding.isCompl_tangentRange_orthogonal`: `W_x` and `W_x^ω` are complements;
  `TauCeti.SmoothEmbedding.pullbackComplexStructure_mem_orthogonal`: `W_x^ω` is `Jf`-invariant.
* `TauCeti.SmoothEmbedding.isNondegenerate_compMFDeriv`,
  `TauCeti.SmoothEmbedding.compMFDeriv_pos`;
  `TauCeti.SmoothEmbedding.volumeOrientation_compMFDeriv`: on a surface, the symplectic
  orientation of `ω(df ·, df ·)` is the orientation given by `J`.
* `TauCeti.SmoothEmbedding.normalForm_normalClass`,
  `TauCeti.SmoothEmbedding.compatible_normalForm`.
* `TauCeti.SmoothEmbedding.contMDiff_normalSplitting`: the splitting is smooth on total spaces;
  `TauCeti.SmoothEmbedding.pushforward_normalSplitting`: it carries `ω` to
  `(ω.compMFDeriv f f.contMDiff).prod (normalForm f hdim hJ ω hω)`.

## Implementation notes

The construction parallels Tau Ceti's symplectic normal bundle of a symplectic submanifold,
`TauCeti.SmoothEmbedding.normalSpaceSymplecticComplementEquiv`,
`TauCeti.SmoothEmbedding.symplecticNormalRepresentative` and
`TauCeti.SmoothEmbedding.symplecticNormalForm`
(`TauCeti/Geometry/Symplectic/Lagrangian/Embedding/Symplectic/Normal.lean`), whose pointwise API it
mirrors. Those need a nondegenerate form on the tangent bundle of all of `X`, and here the form
lives only on `f *ᵖ TX`, so they are not used. Both are instances of Tau Ceti's
`TauCeti.SmoothEmbedding.complementRepresentative`.

The complement `W^ω` comes from Tau Ceti's
`TauCeti.SymplecticForm.Tames.isSymplectic_of_mem_invtSubmodule`. The projection onto `W` along
`W^ω` is smooth by
`TauCeti.HasLocalContMDiffSubbundleFrames.contMDiff_totalSpace_projection_orthogonal`
(`SymplecticGeometry/Geometry/Manifold/VectorBundle/Orthogonal.lean`), applied to the frames of
`W` (`Bundle.Pullback.hasLocalContMDiffSubbundleFrames_range_mfderiv`) and the flat maps of `ω`,
as in `SymplecticGeometry/Geometry/Symplectic/Neighborhood/Frames.lean` for an ambient form. The
representatives in `W^ω` are then smooth on the normal bundle by Tau Ceti's
`TauCeti.SmoothEmbedding.contMDiff_normalBundle_iff`. The inverse of the splitting,
`(u, a) ↦ df u + r a`, is smooth on total spaces, and so is the splitting by
`contMDiff_hom_bundle_symm`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Example 4.4.5 and §3.4 (the symplectic normal bundle).
-/

public section

noncomputable section

open _root_.Bundle Module
open scoped Manifold

namespace TauCeti.SmoothEmbedding

open SymplecticGeometry.Bundle
open TauCeti.SmoothAlmostComplexStructure (pullbackComplexStructure_apply)

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) X]
  {E' H' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
  {hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0}
  (f : SmoothEmbedding I' I ((⊤ : ℕ∞) : WithTop ℕ∞) M X) {J : SmoothAlmostComplexStructure I X}

/-! ### The pulled-back complex structure -/

variable {f} in
/-- If the tangent images of `f` are `J`-invariant, they are invariant under the pull-back of
`J`. -/
theorem pullbackComplexStructure_mem_tangentRange
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn)) {x : M}
    {v : ((f : M → X) *ᵖ (TangentSpace I)) x} (hv : v ∈ f.isImmersion.tangentRange x hn) :
    J.pullbackComplexStructure f f.contMDiff x v ∈ f.isImmersion.tangentRange x hn :=
  (congrArg (· ∈ f.isImmersion.tangentRange x hn)
      (J.pullbackComplexStructure_apply f f.contMDiff x v)).mpr
    (hJ x hv)

/-! ### The tangent image and its orthogonal -/

variable {f} {ω : ContMDiffTwoForm I' ⊤ E ((f : M → X) *ᵖ (TangentSpace I))}

variable (f) in
/-- The `ω`-orthogonal of the tangent image at `x`: the vectors `v` of `T_{f x} X` with
`ω(w, v) = 0` for every vector `w` tangent to the image of `f`. -/
def orthogonalTangentRange (ω : ContMDiffTwoForm I' ⊤ E ((f : M → X) *ᵖ (TangentSpace I)))
    (x : M) (hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) : Submodule ℝ (TangentSpace I (f x)) :=
  (ω.bilinFormAt x).orthogonal (f.isImmersion.tangentRange x hn)

variable (f) in
theorem orthogonalTangentRange_def
    (ω : ContMDiffTwoForm I' ⊤ E ((f : M → X) *ᵖ (TangentSpace I))) (x : M)
    (hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) :
    f.orthogonalTangentRange ω x hn = (ω.bilinFormAt x).orthogonal
        (f.isImmersion.tangentRange x hn) :=
  (rfl)

/-- A vector `v` lies in the `ω`-orthogonal of the tangent image exactly when `ω(w, v) = 0` for
every vector `w` of the tangent image. -/
theorem mem_orthogonalTangentRange_iff {x : M} {v : TangentSpace I (f x)} :
    v ∈ f.orthogonalTangentRange ω x hn ↔
      ∀ w ∈ f.isImmersion.tangentRange x hn, ω.bilinFormAt x w v = 0 :=
  Iff.rfl

variable [FiniteDimensional ℝ E]

/-- If the tangent images of `f` are `J`-invariant and `ω` tames the pull-back of `J`, then at
each point the tangent image and its `ω`-orthogonal are complements. -/
theorem isCompl_tangentRange_orthogonal
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) (x : M) :
    IsCompl (f.isImmersion.tangentRange x hn) (f.orthogonalTangentRange ω x hn) := by
  have : FiniteDimensional ℝ (((f : M → X) *ᵖ (TangentSpace I)) x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  have h := ((hω.isNondegenerate.tames_iff.1 hω x).isSymplectic_of_mem_invtSubmodule
    (L := f.isImmersion.tangentRange x hn) ((Module.End.mem_invtSubmodule _).2 fun v hv ↦
        ?_)).isCompl
  · -- The fibre of the pull-back carries the module structure of `TangentSpace I (f x)` under
    -- another name, so the rewrite needs `erw`.
    erw [TauCeti.SymplecticForm.orthogonal_def,
      ContMDiffTwoForm.IsNondegenerate.toBilinForm_symplecticFormAt] at h
    exact h
  rw [Submodule.mem_comap, ContMDiffComplexStructure.almostComplexStructureAt_toLinearMap]
  exact pullbackComplexStructure_mem_tangentRange hJ hv

/-- The tangent image and its `ω`-orthogonal are topological complements. -/
theorem isTopCompl_tangentRange_orthogonal
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) (x : M) :
    (f.isImmersion.tangentRange x hn).IsTopCompl (f.orthogonalTangentRange ω x hn) :=
  have : FiniteDimensional ℝ (((f : M → X) *ᵖ (TangentSpace I)) x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  ⟨isCompl_tangentRange_orthogonal hJ hω x, LinearMap.continuous_of_finiteDimensional _⟩

omit [FiniteDimensional ℝ E] in
/-- If the tangent images of `f` are `J`-invariant and `ω` is invariant under the pull-back of
`J`, then the `ω`-orthogonal of each tangent image is invariant under it. -/
theorem pullbackComplexStructure_mem_orthogonal
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Invariant (J.pullbackComplexStructure f f.contMDiff)) {x : M}
    {v : ((f : M → X) *ᵖ (TangentSpace I)) x}
    (hv : v ∈ f.orthogonalTangentRange ω x hn) :
    J.pullbackComplexStructure f f.contMDiff x v ∈ f.orthogonalTangentRange ω x hn := by
  refine mem_orthogonalTangentRange_iff.2 fun w hw ↦ ?_
  -- `J w` is tangent, and `ω(-w, J v) = ω(J (J w), J v) = ω(J w, v) = 0`.
  have h :=
    ContMDiffTwoForm.invariant_def.1 hω x (J.pullbackComplexStructure f f.contMDiff x w) v
  -- `w` is a vector of `TangentSpace I (f x)`, the fibre of the pull-back under another name.
  erw [ContMDiffComplexStructure.apply_apply, map_neg, LinearMap.neg_apply,
    mem_orthogonalTangentRange_iff.1 hv _ (pullbackComplexStructure_mem_tangentRange hJ hw),
    neg_eq_zero] at h
  exact h

variable [FiniteDimensional ℝ E'] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ### The form on the tangent bundle -/

omit [FiniteDimensional ℝ E] in
/-- If `ω` tames the pull-back of `J`, the form `ω(df ·, df ·)` on the tangent bundle is positive
on every pair `(u, v)` with `u ≠ 0` and `df v = J (df u)`. -/
theorem compMFDeriv_pos (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) {x : M}
    {u v : TangentSpace I' x} (hu : u ≠ 0)
    (hv : mfderiv I' I f x v = J (f x) (mfderiv I' I f x u)) :
    0 < (ω.compMFDeriv f f.contMDiff).bilinFormAt x u v := by
  rw [ContMDiffTwoForm.bilinFormAt_compMFDeriv, hv,
    ← pullbackComplexStructure_apply J f f.contMDiff]
  exact ContMDiffTwoForm.tames_def.1 hω x _ fun h ↦
    hu (f.isImmersion.mfderiv_injective (by simp) x (h.trans (map_zero _).symm))

omit [FiniteDimensional ℝ E] in
/-- If the tangent images of `f` are `J`-invariant and `ω` tames the pull-back of `J`, the form
`ω(df ·, df ·)` on the tangent bundle is nondegenerate. -/
theorem isNondegenerate_compMFDeriv
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) :
    (ω.compMFDeriv f f.contMDiff).IsNondegenerate := by
  rw [ContMDiffTwoForm.isNondegenerate_iff_separatingLeft]
  intro x u hu
  by_contra h0
  obtain ⟨v, hv⟩ := hJ x ⟨u, rfl⟩
  have h := compMFDeriv_pos hω h0 hv
  rw [ContMDiffTwoForm.bilinFormAt_apply] at h
  exact h.ne' (hu v)

omit [FiniteDimensional ℝ E] in
/-- **The area form induced by a taming form gives the orientation of `J`.** Let `f` embed a
surface `M` so that `J` preserves its tangent planes, and let `ω` be a two-form on `f *ᵖ TX`
that tames the pull-back of `J`. If `o` is the orientation of `M` for which every basis `(u, v)`
of `T_c M` with `df v = J (df u)` is positive, then `o` is the symplectic orientation of the
nondegenerate two-form `ω(df ·, df ·)` on `M`. -/
theorem volumeOrientation_compMFDeriv (hE' : finrank ℝ E' = 2)
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff))
    {o : Manifold.Orientation I' M (Fin 2)}
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)),
      mfderiv I' I f c (b 1) = J (f c) (mfderiv I' I f c (b 0)) →
        b.orientation = o.orientationAt c) :
    (ContMDiffTwoForm.isNondegenerate_tangentEquiv_iff.2
        (isNondegenerate_compMFDeriv hJ hω)).volumeOrientation (n := 1) hE' = o := by
  have : Nontrivial E' := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  ext x
  -- A frame `(u, v)` with `df v = J (df u)` is positive for `o`, and `ω(df u, df v) > 0`.
  obtain ⟨u, hu⟩ := exists_ne (0 : TangentSpace I' x)
  obtain ⟨v, hv⟩ := hJ x ⟨u, rfl⟩
  have hpos := compMFDeriv_pos hω hu hv
  have hli : LinearIndependent ℝ ![u, v] :=
    ((ω.compMFDeriv f f.contMDiff).isAlt_bilinFormAt x)
      |>.linearIndependent_pair_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hpos.ne')
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simpa using hE'.symm)
  have hb : ⇑b = ![u, v] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  rw [← ho x b (by simpa [hb] using hv)]
  refine ((SmoothTwoForm.IsNondegenerate.orientation_eq_orientationAt_volumeOrientation_iff
    (ContMDiffTwoForm.isNondegenerate_tangentEquiv_iff.2 (isNondegenerate_compMFDeriv hJ hω))
    (n := 1) hE' b).2 ?_).symm
  rw [SmoothTwoForm.volumeForm_one, ContMDiffTwoForm.tangentEquiv_apply, hb,
    ← ContMDiffTwoForm.bilinFormAt_apply]
  exact hpos

/-! ### The projection onto the tangent image -/

omit [FiniteDimensional ℝ E'] in
/-- If the tangent images of `f` are `J`-invariant and `ω` tames the pull-back of `J`, the
projection of `f *ᵖ TX` onto the tangent images along their `ω`-orthogonals is a smooth map of
the total space of `f *ᵖ TX` to itself. -/
theorem contMDiff_projection_orthogonalTangentRange
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) :
    ContMDiff (I'.prod 𝓘(ℝ, E)) (I'.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : TotalSpace E ((f : M → X) *ᵖ (TangentSpace I)) ↦
        TotalSpace.mk' E (E := (f : M → X) *ᵖ (TangentSpace I)) p.proj
          ((f.isImmersion.tangentRange p.proj hn).projection _
            (isCompl_tangentRange_orthogonal hJ hω p.proj) p.snd)) := by
  have hc (x : M) : IsCompl (f.isImmersion.tangentRange x hn)
      (LinearMap.BilinForm.orthogonal (ω.flat x).toLinearMap₁₂ (f.isImmersion.tangentRange x hn)) :=
    (ContMDiffTwoForm.orthogonal_flat ω x _).symm ▸ isCompl_tangentRange_orthogonal hJ hω x
  have h := (_root_.Bundle.Pullback.hasLocalContMDiffSubbundleFrames_range_mfderiv f
    f.isImmersion).contMDiff_totalSpace_projection_orthogonal ω.contMDiff_flat hc
  refine h.congr fun p ↦ congrArg (TotalSpace.mk p.proj) ?_
  -- The two projections differ only in the name of the complement.
  have key {q q' : Submodule ℝ (TangentSpace I (f p.proj))} (hq : q = q')
      (h₁ : IsCompl (f.isImmersion.tangentRange p.proj hn) q)
          (h₂ : IsCompl (f.isImmersion.tangentRange p.proj hn) q') :
      (f.isImmersion.tangentRange p.proj hn).projection q h₁ =
          (f.isImmersion.tangentRange p.proj hn).projection q' h₂ := by
    subst hq
    rfl
  exact LinearMap.congr_fun (key (ContMDiffTwoForm.orthogonal_flat ω p.proj _).symm _ _) p.snd

/-! ### Representatives of normal classes in the orthogonal -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The representatives in the `ω`-orthogonals of the normal classes form a smooth map from the
total space of the normal bundle to that of `f *ᵖ TX`. -/
theorem contMDiff_complementRepresentative_orthogonalTangentRange
    (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) :
    letI := f.normalSpaceFiberBundle hn hdim
    ContMDiff (I'.prod 𝓘(ℝ, P)) (I'.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : TotalSpace P (fun x ↦ f.isImmersion.NormalSpace x hn) ↦
        TotalSpace.mk' E (E := (f : M → X) *ᵖ (TangentSpace I)) p.proj
          (f.complementRepresentative p.proj hn (isTopCompl_tangentRange_orthogonal hJ hω p.proj)
            p.snd)) := by
  let := f.normalSpaceFiberBundle hn hdim
  refine (f.contMDiff_normalBundle_iff hn (by simp) hdim _).2 ?_
  refine (ContMDiff.sub_sectionAlong (b := TotalSpace.proj)
    (s := fun p : TotalSpace E ((f : M → X) *ᵖ (TangentSpace I)) ↦ p.snd) contMDiff_id
    (contMDiff_projection_orthogonalTangentRange hJ hω)).congr fun p ↦ ?_
  rw [Function.comp_apply, normalQuotientMap_apply]
  refine congrArg (TotalSpace.mk p.proj) ?_
  dsimp only
  have h := complementRepresentative_normalClass f p.proj hn
    (isTopCompl_tangentRange_orthogonal hJ hω p.proj) p.snd
  -- `p.snd` is a vector of the pull-back, `TangentSpace I (f p.proj)` under another name.
  erw [Submodule.projection_eq_self_sub_projection (isCompl_tangentRange_orthogonal hJ hω p.proj)]
    at h
  exact h

/-! ### The splitting -/

omit [FiniteDimensional ℝ E'] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M] in
variable (f) in
/-- The splitting of `f *ᵖ TX` at `x` along the tangent image and its `ω`-orthogonal: the
isomorphism `v ↦ ((df)⁻¹ P v, [v])` onto `T_x M × ν_x`, with `P` the projection onto the tangent
image along its `ω`-orthogonal. It is the inverse of
`TauCeti.SmoothEmbedding.tangentNormalEquiv` for the representatives in the `ω`-orthogonal. -/
def normalSplitting (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
    (f.isImmersion.tangentRange x hn))
    (ω : ContMDiffTwoForm I' ⊤ E ((f : M → X) *ᵖ (TangentSpace I)))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) (x : M) :
    ((f : M → X) *ᵖ (TangentSpace I)) x ≃L[ℝ]
      (TangentSpace I' ×ᵇ fun x ↦ f.isImmersion.NormalSpace x hn) x :=
  (f.tangentNormalEquiv hn
    (fun x ↦ f.complementRepresentative x hn (isTopCompl_tangentRange_orthogonal hJ hω x))
    (fun x ↦ f.normalClass_complementRepresentative x hn _) x).symm

omit [FiniteDimensional ℝ E'] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M] in
/-- The inverse of the splitting sends `(u, a)` to `df u + r a`, with `r a` the representative of
`a` in the `ω`-orthogonal of the tangent image. -/
@[simp]
theorem normalSplitting_symm_apply
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) (x : M)
    (p : (TangentSpace I' ×ᵇ fun x ↦ f.isImmersion.NormalSpace x hn) x) :
    (f.normalSplitting hJ ω hω x).symm p = mfderiv I' I f x p.1 +
      f.complementRepresentative x hn (isTopCompl_tangentRange_orthogonal hJ hω x) p.2 := by
  rw [normalSplitting, ContinuousLinearEquiv.symm_symm, tangentNormalEquiv_apply]

omit [FiniteDimensional ℝ E'] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M] in
/-- The normal component of the splitting is the normal class. -/
@[simp]
theorem snd_normalSplitting_apply
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) (x : M)
    (v : TangentSpace I (f x)) :
    (f.normalSplitting hJ ω hω x v).2 = f.isImmersion.normalClass x hn v := by
  rw [normalSplitting, snd_tangentNormalEquiv_symm_apply]

omit [FiniteDimensional ℝ E'] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M] in
/-- The tangential component of the splitting is carried by `df` to the projection onto the
tangent image along its `ω`-orthogonal. -/
theorem mfderiv_fst_normalSplitting_apply
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) (x : M)
    (v : TangentSpace I (f x)) :
    mfderiv I' I f x (f.normalSplitting hJ ω hω x v).1 =
      (f.isImmersion.tangentRange x hn).projection _ (isCompl_tangentRange_orthogonal hJ hω x)
          v := by
  rw [normalSplitting, mfderiv_fst_tangentNormalEquiv_symm_apply,
    complementRepresentative_normalClass,
    Submodule.projection_eq_self_sub_projection (isCompl_tangentRange_orthogonal hJ hω x),
    sub_sub_cancel]

/-- The splitting is a smooth map from the total space of `f *ᵖ TX` to that of `TM ×ᵇ ν`. -/
theorem contMDiff_normalSplitting (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ContMDiff (I'.prod 𝓘(ℝ, E)) (I'.prod 𝓘(ℝ, E' × P)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : TotalSpace E ((f : M → X) *ᵖ (TangentSpace I)) ↦
        TotalSpace.mk' (E' × P) (E := TangentSpace I' ×ᵇ fun x ↦ f.isImmersion.NormalSpace x hn)
            p.proj
          (f.normalSplitting hJ ω hω p.proj p.snd)) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  -- The inverse `(u, a) ↦ df u + r a` is smooth on total spaces.
  have hΨ : ContMDiff (I'.prod 𝓘(ℝ, E' × P)) (I'.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : TotalSpace (E' × P) (TangentSpace I' ×ᵇ fun x ↦ f.isImmersion.NormalSpace x hn) ↦
        TotalSpace.mk' E (E := (f : M → X) *ᵖ (TangentSpace I)) p.proj
          ((f.normalSplitting hJ ω hω p.proj).symm p.snd)) := by
    have h₁ := (_root_.Bundle.Pullback.contMDiff_totalSpace_mfderiv f f.contMDiff).comp
      (_root_.Bundle.Prod.contMDiff_fst (E₁ := TangentSpace I')
        (E₂ := fun x ↦ f.isImmersion.NormalSpace x hn) (F₁ := E') (F₂ := P)
            (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
    have h₂ := (contMDiff_complementRepresentative_orthogonalTangentRange hdim hJ hω).comp
      (_root_.Bundle.Prod.contMDiff_snd (E₁ := TangentSpace I')
        (E₂ := fun x ↦ f.isImmersion.NormalSpace x hn) (F₁ := E') (F₂ := P)
            (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
    refine (h₁.add_sectionAlong h₂).congr fun p ↦ ?_
    exact congrArg (TotalSpace.mk p.proj) (normalSplitting_symm_apply hJ hω p.proj p.snd)
  have h :=
    SymplecticGeometry.contMDiff_hom_bundle_symm (fun x ↦ (f.normalSplitting hJ ω hω x).symm) hΨ
  simp only [ContinuousLinearEquiv.symm_symm] at h
  exact (TauCeti.contMDiff_hom_bundle_iff _).1 h

/-! ### The form on the normal bundle -/

variable (f) in
/-- The two-form `ω_ν(a, b) = ω(r a, r b)` on the normal bundle, with `r a` the representative of
`a` in the `ω`-orthogonal of the tangent image. -/
def normalForm (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (ω : ContMDiffTwoForm I' ⊤ E ((f : M → X) *ᵖ (TangentSpace I)))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ContMDiffTwoForm I' ⊤ P (fun x ↦ f.isImmersion.NormalSpace x hn) :=
  letI := f.normalSpaceFiberBundle hn hdim
  letI := f.normalSpaceVectorBundle hn hdim
  ContMDiffTwoForm.compContinuousLinearMap (V := (f : M → X) *ᵖ (TangentSpace I))
    (V₂ := fun x ↦ f.isImmersion.NormalSpace x hn)
    (fun x ↦ f.complementRepresentative x hn (isTopCompl_tangentRange_orthogonal hJ hω x))
    ((TauCeti.contMDiff_hom_bundle_iff (E₁ := fun x ↦ f.isImmersion.NormalSpace x hn)
      (E₂ := (f : M → X) *ᵖ (TangentSpace I)) _).2
        (contMDiff_complementRepresentative_orthogonalTangentRange hdim hJ hω)) ω

variable (f) in
theorem normalForm_def (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (ω : ContMDiffTwoForm I' ⊤ E ((f : M → X) *ᵖ (TangentSpace I)))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    f.normalForm hdim hJ ω hω =
      ContMDiffTwoForm.compContinuousLinearMap (V := (f : M → X) *ᵖ (TangentSpace I))
        (V₂ := fun x ↦ f.isImmersion.NormalSpace x hn)
        (fun x ↦ f.complementRepresentative x hn (isTopCompl_tangentRange_orthogonal hJ hω x))
        ((TauCeti.contMDiff_hom_bundle_iff (E₁ := fun x ↦ f.isImmersion.NormalSpace x hn)
      (E₂ := (f : M → X) *ᵖ (TangentSpace I)) _).2
        (contMDiff_complementRepresentative_orthogonalTangentRange hdim hJ hω))
        ω :=
  (rfl)

/-- The form on the normal bundle at `x` is `ω_x(r ·, r ·)`, with `r` the representative map into
the `ω`-orthogonal of the tangent image. -/
@[simp]
theorem normalForm_apply (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) (x : M) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    f.normalForm hdim hJ ω hω x = (ω x).compContinuousLinearMap
      (f.complementRepresentative x hn (isTopCompl_tangentRange_orthogonal hJ hω x)) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  rw [normalForm_def]
  exact ContMDiffTwoForm.compContinuousLinearMap_apply
      (V₂ := fun x ↦ f.isImmersion.NormalSpace x hn) _ _ ω x

/-- The form on the normal bundle takes on `a`, `b` the value of `ω` on their representatives in
the `ω`-orthogonal of the tangent image. -/
theorem bilinFormAt_normalForm (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) (x : M)
    (a b : f.isImmersion.NormalSpace x hn) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (f.normalForm hdim hJ ω hω).bilinFormAt x a b = ω.bilinFormAt x
      (f.complementRepresentative x hn (isTopCompl_tangentRange_orthogonal hJ hω x) a)
      (f.complementRepresentative x hn (isTopCompl_tangentRange_orthogonal hJ hω x) b) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  rw [normalForm_def]
  exact ContMDiffTwoForm.bilinFormAt_compContinuousLinearMap
      (V₂ := fun x ↦ f.isImmersion.NormalSpace x hn)
    _ _ ω x a b

/-- On the normal classes of two vectors of the `ω`-orthogonal of the tangent image, the form on
the normal bundle is `ω`. -/
theorem normalForm_normalClass (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) {x : M}
    {v w : TangentSpace I (f x)}
    (hv : v ∈ f.orthogonalTangentRange ω x hn) (hw : w ∈ f.orthogonalTangentRange ω x hn) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (f.normalForm hdim hJ ω hω).bilinFormAt x (f.isImmersion.normalClass x hn v)
        (f.isImmersion.normalClass x hn w) =
      ω.bilinFormAt x v w := by
  rw [bilinFormAt_normalForm, complementRepresentative_normalClass_of_mem _ _ _ _ hv,
    complementRepresentative_normalClass_of_mem _ _ _ _ hw]

omit [FiniteDimensional ℝ E'] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M] in
/-- The representative in the `ω`-orthogonal of the image of `a` under the complex structure
induced by `J` on the normal space is the image under `J` of the representative of `a`. -/
private theorem complementRepresentative_normalComplexStructureAt
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Compatible (J.pullbackComplexStructure f f.contMDiff)) (x : M)
    (a : f.isImmersion.NormalSpace x hn) :
    f.complementRepresentative x hn (isTopCompl_tangentRange_orthogonal hJ hω.tames x)
        (f.normalComplexStructureAt hn J x (hJ x) a) =
      J (f x) (f.complementRepresentative x hn (isTopCompl_tangentRange_orthogonal hJ hω.tames x)
        a) := by
  rw [complementRepresentative_eq_iff, ← pullbackComplexStructure_apply J f f.contMDiff]
  refine ⟨pullbackComplexStructure_mem_orthogonal hJ hω.invariant
    (complementRepresentative_mem _ _ _ _ _), ?_⟩
  rw [pullbackComplexStructure_apply,
    ← normalComplexStructureAt_normalClass (hJ x),
    normalClass_complementRepresentative]

/-- If `ω` is compatible with the pull-back of `J`, the form on the normal bundle is compatible
with the complex structure that `J` induces on the normal bundle. -/
theorem compatible_normalForm (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Compatible (J.pullbackComplexStructure f f.contMDiff)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    (f.normalForm hdim hJ ω hω.tames).Compatible (f.contMDiffNormalComplexStructure hdim J hJ) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  refine ⟨ContMDiffTwoForm.invariant_def.2 fun x a b ↦ ?_,
    ContMDiffTwoForm.tames_def.2 fun x a ha ↦ ?_⟩
  · rw [contMDiffNormalComplexStructure_apply, contMDiffNormalComplexStructure_apply,
      bilinFormAt_normalForm, bilinFormAt_normalForm,
      complementRepresentative_normalComplexStructureAt hJ hω,
      complementRepresentative_normalComplexStructureAt hJ hω,
      ← pullbackComplexStructure_apply J f f.contMDiff,
      ← pullbackComplexStructure_apply J f f.contMDiff]
    exact ContMDiffTwoForm.invariant_def.1 hω.invariant x _ _
  · rw [contMDiffNormalComplexStructure_apply, bilinFormAt_normalForm,
      complementRepresentative_normalComplexStructureAt hJ hω,
      ← pullbackComplexStructure_apply J f f.contMDiff]
    refine ContMDiffTwoForm.tames_def.1 hω.tames x _ fun h ↦ ha ?_
    exact complementRepresentative_injective _ _ _ _ (h.trans (map_zero _).symm)

/-! ### The splitting is symplectic -/

/-- The splitting carries `ω` to the direct sum of the form on the tangent bundle and the form on
the normal bundle: `(f *ᵖ TX, ω)` is the direct sum of `(TM, σ)` and `(ν, ω_ν)`. -/
theorem pushforward_normalSplitting (hdim : finrank ℝ P = finrank ℝ E - finrank ℝ E')
    (hJ : ∀ x, Set.MapsTo (J (f x)) (f.isImmersion.tangentRange x hn)
        (f.isImmersion.tangentRange x hn))
    (hω : ω.Tames (J.pullbackComplexStructure f f.contMDiff)) :
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ContMDiffTwoForm.pushforward (f.normalSplitting hJ ω hω)
        (contMDiff_normalSplitting hdim hJ hω) ω =
      (ω.compMFDeriv f f.contMDiff).prod (f.normalForm hdim hJ ω hω) := by
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  refine (ContMDiffTwoForm.pushforward_eq_iff _ _).2 fun x v w ↦ ?_
  obtain ⟨p, rfl⟩ := (f.normalSplitting hJ ω hω x).symm.surjective v
  obtain ⟨q, rfl⟩ := (f.normalSplitting hJ ω hω x).symm.surjective w
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply,
    ContMDiffTwoForm.bilinFormAt_prod_apply, ContMDiffTwoForm.bilinFormAt_compMFDeriv,
    bilinFormAt_normalForm,
    normalSplitting_symm_apply, normalSplitting_symm_apply]
  -- The cross terms vanish: a tangent vector and a vector of the `ω`-orthogonal pair to zero.
  have h₁ := mem_orthogonalTangentRange_iff.1
    (complementRepresentative_mem _ _ _ (isTopCompl_tangentRange_orthogonal hJ hω x) q.2) _
      ⟨p.1, rfl⟩
  have h₂ := (ω.isAlt_bilinFormAt x).isRefl _ _ (mem_orthogonalTangentRange_iff.1
    (complementRepresentative_mem _ _ _ (isTopCompl_tangentRange_orthogonal hJ hω x) p.2) _
      ⟨q.1, rfl⟩)
  -- The sums are taken in `TangentSpace I (f x)`, the fibre of the pull-back under another name,
  -- so expanding the bilinear form needs `erw`.
  erw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply]
  erw [h₁, h₂, add_zero, zero_add]

end TauCeti.SmoothEmbedding

end
