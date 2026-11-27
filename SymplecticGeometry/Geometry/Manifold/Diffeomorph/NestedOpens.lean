/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Open subsets of an open subset, read in the ambient manifold

Let `W` be an open subset of a manifold `M`, and `V` an open subset of `W`. The image of `V`
under the inclusion `W → M` is an open subset `imageVal V` of `M`, contained in `W`, and `V` is
diffeomorphic to it by `diffeomorphImageVal V`, which keeps every point where it is. This
diffeomorphism and its inverse have identity differential, since the inclusions have.

A diffeomorphism `ψ` between open subsets `V` and `V'` of open subsets `W` and `W'` is read in
the ambient manifolds as the diffeomorphism `ψ.imageValCongr` between `imageVal V` and
`imageVal V'`. It takes the values of `ψ` and has its differentials, and it is equivariant when
`ψ` is.

## Main definitions

* `TopologicalSpace.Opens.imageVal`: the image in `M` of an open subset of `W`.
* `TopologicalSpace.Opens.diffeomorphImageVal`: the diffeomorphism from `V` onto `imageVal V`.
* `Diffeomorph.imageValCongr`: a diffeomorphism between open subsets of open subsets, read in
  the ambient manifolds.

## Main results

* `TopologicalSpace.Opens.mfderiv_diffeomorphImageVal_apply`,
  `TopologicalSpace.Opens.mfderiv_diffeomorphImageVal_symm_apply`: both have identity
  differential.
* `TopologicalSpace.Opens.smul_mem_imageVal`: the image of an invariant open subset is invariant.
* `Diffeomorph.mfderiv_imageValCongr_apply`, `Diffeomorph.mfderiv_imageValCongr_eq_id_iff`,
  `Diffeomorph.imageValCongr_smul`: the transported diffeomorphism has the differentials of `ψ`,
  and is equivariant when `ψ` is.

The two maps of `diffeomorphImageVal`, and the proofs that they are smooth, adapt the private
declarations `toImage`, `ofImage`, `contMDiff_toImage` and `contMDiff_ofImage` of Tau Ceti's
`TauCeti/Geometry/Manifold/Sheaf/Smooth/Restrict.lean`, which treat the image in `M` of an open
subset `V` of `U` as `U.isOpenEmbedding.isOpenMap.functor.obj V`, at smoothness `∞`; here the
image is an `Opens M` and the smoothness is any `n`.
-/

public section

open Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞}

namespace TopologicalSpace.Opens

variable {W : Opens M} (V : Opens W)

/-- The image in `M` of an open subset `V` of an open subset `W` of `M`. -/
def imageVal : Opens M :=
  ⟨Subtype.val '' (V : Set W), W.isOpen.isOpenMap_subtypeVal _ V.isOpen⟩

theorem coe_imageVal : (imageVal V : Set M) = Subtype.val '' (V : Set W) := (rfl)

variable {V} in
@[simp]
theorem mem_imageVal {x : M} : x ∈ imageVal V ↔ ∃ h : x ∈ W, (⟨x, h⟩ : W) ∈ V := by
  rw [← SetLike.mem_coe, coe_imageVal]
  exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ ⟨y.property, hy⟩, fun ⟨h, hx⟩ ↦ ⟨_, hx, rfl⟩⟩

theorem coe_mem_imageVal (y : V) : ((y : W) : M) ∈ imageVal V :=
  ⟨y, y.property, rfl⟩

theorem imageVal_le : imageVal V ≤ W := by
  rintro _ ⟨y, -, rfl⟩
  exact y.property

/-- If `G` acts on `W` so that the inclusion `W → M` is equivariant, the image of a
`G`-invariant open subset of `W` is `G`-invariant. -/
theorem smul_mem_imageVal {G : Type*} [SMul G M] [SMul G W]
    (hc : ∀ (g : G) (x : W), ((g • x : W) : M) = g • (x : M)) {V : Opens W}
    (hV : ∀ (g : G), ∀ x ∈ V, g • x ∈ V) (g : G) {x : M} (hx : x ∈ imageVal V) :
    g • x ∈ imageVal V := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨g • y, hV g y hy, hc g y⟩

/-- An open subset `V` of an open subset `W` of `M` is diffeomorphic to its image in `M`, by the
map that keeps every point where it is. -/
noncomputable def diffeomorphImageVal : V ≃ₘ^n⟮I, I⟯ imageVal V where
  toFun y := ⟨y, coe_mem_imageVal V y⟩
  invFun x := ⟨⟨x, imageVal_le V x.property⟩, (mem_imageVal.1 x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
    (contMDiff_subtypeVal.comp contMDiff_subtypeVal :
      ContMDiff I I n ((Subtype.val : W → M) ∘ (Subtype.val : V → W)))
  contMDiff_invFun := (TauCeti.ContMDiff.subtypeVal_comp_iff _ _).1
    ((TauCeti.ContMDiff.subtypeVal_comp_iff W _).1
      (contMDiff_subtypeVal : ContMDiff I I n (Subtype.val : imageVal V → M)))

@[simp]
theorem coe_diffeomorphImageVal_apply (y : V) :
    (diffeomorphImageVal (I := I) (n := n) V y : M) = y := (rfl)

@[simp]
theorem coe_diffeomorphImageVal_symm_apply (x : imageVal V) :
    (((diffeomorphImageVal (I := I) (n := n) V).symm x : W) : M) = x := (rfl)

/-- The diffeomorphism onto the image, followed by the inclusion of the image in `W`, is the
inclusion of `V` in `W`. -/
theorem inclusion_comp_diffeomorphImageVal :
    inclusion (imageVal_le V) ∘ diffeomorphImageVal (I := I) (n := n) V = Subtype.val :=
  funext fun _ ↦ rfl

/-- The inverse of the diffeomorphism onto the image, followed by the inclusion of `V` in `W`, is
the inclusion of the image in `W`. -/
theorem subtypeVal_comp_diffeomorphImageVal_symm :
    Subtype.val ∘ (diffeomorphImageVal (I := I) (n := n) V).symm = inclusion (imageVal_le V) :=
  funext fun _ ↦ rfl

/-- The diffeomorphism from `V` onto its image has identity differential. -/
theorem mfderiv_diffeomorphImageVal_apply (y : V) (v : TangentSpace I y) :
    mfderiv I I (diffeomorphImageVal (I := I) (n := n) V) y v = v := by
  have h : (Subtype.val : imageVal V → M) ∘ diffeomorphImageVal (I := I) (n := n) V =
      (Subtype.val : W → M) ∘ Subtype.val :=
    funext (coe_diffeomorphImageVal_apply V)
  rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, h,
    TauCeti.Manifold.mfderiv_subtype_val_comp_apply]
  exact TauCeti.Manifold.mfderiv_subtype_val_apply _ _

/-- The inverse of the diffeomorphism from `V` onto its image has identity differential. -/
theorem mfderiv_diffeomorphImageVal_symm_apply (x : imageVal V) (v : TangentSpace I x) :
    mfderiv I I (diffeomorphImageVal (I := I) (n := n) V).symm x v = v := by
  rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, subtypeVal_comp_diffeomorphImageVal_symm,
    TauCeti.Manifold.mfderiv_inclusion_apply]

end TopologicalSpace.Opens

namespace Diffeomorph

open TopologicalSpace Opens

variable {W : Opens M} {W' : Opens N} {V : Opens W} {V' : Opens W'}

/-- A diffeomorphism between open subsets `V` and `V'` of open subsets `W` and `W'`, read as a
diffeomorphism between the images of `V` and `V'` in the ambient manifolds. -/
noncomputable def imageValCongr (ψ : V ≃ₘ^n⟮I, J⟯ V') : imageVal V ≃ₘ^n⟮I, J⟯ imageVal V' :=
  (diffeomorphImageVal V).symm.trans (ψ.trans (diffeomorphImageVal V'))

variable (ψ : V ≃ₘ^n⟮I, J⟯ V')

@[simp]
theorem coe_imageValCongr_apply (x : imageVal V) :
    (ψ.imageValCongr x : N) = ψ ((diffeomorphImageVal (I := I) (n := n) V).symm x) := (rfl)

theorem imageValCongr_apply_diffeomorphImageVal (y : V) :
    (ψ.imageValCongr (diffeomorphImageVal (I := I) (n := n) V y) : N) = ψ y := (rfl)

/-- The transported diffeomorphism, followed by the inclusion of `imageVal V'` in `W'`, is the
inverse of `diffeomorphImageVal V`, followed by `ψ` and the inclusion of `V'` in `W'`. -/
theorem inclusion_comp_imageValCongr :
    Opens.inclusion (imageVal_le V') ∘ ψ.imageValCongr =
      (Subtype.val ∘ ψ) ∘ (diffeomorphImageVal (I := I) (n := n) V).symm :=
  funext fun _ ↦ rfl

/-- The transported diffeomorphism has the differentials of `ψ`. -/
theorem mfderiv_imageValCongr_apply (x : imageVal V) (v : TangentSpace I x) :
    mfderiv I J ψ.imageValCongr x v =
      mfderiv I J ψ ((diffeomorphImageVal (I := I) (n := n) V).symm x) v := by
  -- `diffeomorphImageVal V` is the same map at every smoothness `n`; take it at `∞`, so that
  -- `mfderiv_comp_diffeomorph` needs no hypothesis on `n`.
  have h : (Subtype.val : imageVal V' → N) ∘ ψ.imageValCongr =
      ((Subtype.val : W' → N) ∘ (Subtype.val ∘ ψ)) ∘
        (diffeomorphImageVal (I := I) (n := ∞) V).symm :=
    funext fun _ ↦ rfl
  rw [← TauCeti.Manifold.mfderiv_subtype_val_comp_apply, h,
    Diffeomorph.mfderiv_comp_diffeomorph _ (by simp), ContinuousLinearMap.comp_apply,
    mfderiv_diffeomorphImageVal_symm_apply]
  exact (TauCeti.Manifold.mfderiv_subtype_val_comp_apply _).trans
    (TauCeti.Manifold.mfderiv_subtype_val_comp_apply _)

/-- A diffeomorphism between open subsets of open subsets of `M` has identity differential at a
point exactly when its transport to the ambient manifold has. -/
theorem mfderiv_imageValCongr_eq_id_iff {W' : Opens M} {V' : Opens W'} (ψ : V ≃ₘ^n⟮I, I⟯ V')
    (x : imageVal V) :
    mfderiv I I ψ.imageValCongr x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) ↔
      mfderiv I I ψ ((diffeomorphImageVal (I := I) (n := n) V).symm x) =
        ContinuousLinearMap.id 𝕜 (TangentSpace I ((diffeomorphImageVal V).symm x)) := by
  constructor <;> intro h <;> ext v
  · -- Both identities act on the model space `E`.
    exact (ψ.mfderiv_imageValCongr_apply x v).symm.trans (congrArg (· v) h)
  · exact (ψ.mfderiv_imageValCongr_apply x v).trans (congrArg (· v) h)

/-- If `G` acts on `W` and `W'` with equivariant inclusions, and `ψ` is equivariant, then so is
the transported diffeomorphism. -/
theorem imageValCongr_smul {G : Type*} [SMul G M] [SMul G W] [SMul G N] [SMul G W']
    (hc : ∀ (g : G) (x : W), ((g • x : W) : M) = g • (x : M))
    (hc' : ∀ (g : G) (x : W'), ((g • x : W') : N) = g • (x : N))
    (hψ : ∀ (g : G) (y : V) (hy : g • (y : W) ∈ V), (ψ ⟨g • (y : W), hy⟩ : W') = g • (ψ y : W'))
    (g : G) (x : imageVal V) (hx : g • (x : M) ∈ imageVal V) :
    (ψ.imageValCongr ⟨g • (x : M), hx⟩ : N) = g • (ψ.imageValCongr x : N) := by
  obtain ⟨y, rfl⟩ : ∃ y, diffeomorphImageVal (I := I) (n := n) V y = x :=
    ⟨_, apply_symm_apply _ x⟩
  have hy : g • (y : W) ∈ V := by
    obtain ⟨h, hm⟩ := mem_imageVal.1 hx
    have : (⟨_, h⟩ : W) = g • (y : W) := Subtype.ext (by simp [hc])
    exact this ▸ hm
  have hgy : (⟨g • ((diffeomorphImageVal (I := I) (n := n) V y : imageVal V) : M), hx⟩ :
      imageVal V) = diffeomorphImageVal (I := I) (n := n) V ⟨g • (y : W), hy⟩ :=
    Subtype.ext (by simp [hc])
  rw [hgy, imageValCongr_apply_diffeomorphImageVal, imageValCongr_apply_diffeomorphImageVal,
    hψ g y hy, hc']

end Diffeomorph

end
