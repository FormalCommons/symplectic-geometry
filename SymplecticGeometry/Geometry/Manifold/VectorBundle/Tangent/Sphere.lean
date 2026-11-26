/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Gradient
public import TauCeti.Topology.VectorBundle.Hom
import TauCeti.Analysis.InnerProductSpace.LinearIsometry

/-!
# The tangent bundle of the sphere plus a trivial line

Let `E` be a real inner product space of dimension `m + 1`, and `S = sphere (0 : E) 1` its unit
sphere, a manifold over `𝓡 m`. At `x ∈ S`, the differential `dι` of the inclusion `ι : S → E`
maps `T_x S` isometrically onto the orthogonal complement of `x` (Tau Ceti's
`TauCeti.sphereTangentEquiv`), so `(v, t) ↦ dι(v) + t • x` is a linear isomorphism
`T_x S × ℝ ≃ E`. Together these give a homeomorphism from the total space of the Whitney sum of
`TS` with the trivial line bundle to that of the trivial bundle with fibre `E`: the tangent
bundle of a sphere is stably trivial.

## Main definitions

* `SymplecticGeometry.sphereTangentProdEquiv m x`: the isomorphism `T_x S × ℝ ≃L[ℝ] E`,
  `(v, t) ↦ dι(v) + t • x`, whose inverse is `w ↦ (dι⁻¹(P w), ⟪x, w⟫)`, with `P` the
  orthogonal projection onto `(ℝ ∙ x)ᗮ`, so that `P w = w - ⟪x, w⟫ • x`.
* `SymplecticGeometry.sphereTangentProdHomeomorph E m`: the homeomorphism from the total space
  of `TangentSpace (𝓡 m) ×ᵇ Bundle.Trivial S ℝ` to that of `Bundle.Trivial S E` that is
  `sphereTangentProdEquiv m x` on the fibre over each `x`.

The forward map is continuous since the tangent map of the inclusion is
(`TauCeti.contMDiff_coe_sphereTangentEquiv`). Tau Ceti's `TauCeti.bundleHomeomorph` then gives
the homeomorphism: since the fibres are finite-dimensional, the inverse is continuous too.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974) (the tangent and normal bundles of the sphere).
-/

public section

open Bundle Metric Module
open scoped Manifold InnerProductSpace

noncomputable section

namespace SymplecticGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {m : ℕ} [Fact (finrank ℝ E = m + 1)]

variable (m) in
/-- At a point `x` of the unit sphere, the isomorphism `T_x S × ℝ ≃ E` sending `(v, t)` to
`dι(v) + t • x`, where `dι` is the differential of the inclusion of the sphere, read through
`TauCeti.sphereTangentEquiv`. -/
def sphereTangentProdEquiv (x : sphere (0 : E) 1) :
    (TangentSpace (𝓡 m) x × ℝ) ≃L[ℝ] E :=
  { toFun p := (TauCeti.sphereTangentEquiv x p.1 : E) + p.2 • (x : E)
    invFun w := ((TauCeti.sphereTangentEquiv x).symm
      ((ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto w), ⟪(x : E), w⟫_ℝ)
    map_add' p q := by
      simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add, add_smul]
      abel
    map_smul' c p := by
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Submodule.coe_smul, smul_eq_mul,
        RingHom.id_apply, smul_add, mul_smul]
    left_inv p := by
      obtain ⟨v, t⟩ := p
      have hv : ⟪(x : E), (TauCeti.sphereTangentEquiv x v : E)⟫_ℝ = 0 :=
        Submodule.mem_orthogonal_singleton_iff_inner_right.1
          (TauCeti.sphereTangentEquiv x v).property
      have hx : ⟪(x : E), (x : E)⟫_ℝ = 1 := by
        rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x, one_pow]
      have ht : ⟪(x : E), (TauCeti.sphereTangentEquiv x v : E) + t • (x : E)⟫_ℝ = t := by
        rw [inner_add_right, real_inner_smul_right, hv, hx, zero_add, mul_one]
      refine Prod.ext ?_ ht
      simp only [Submodule.orthogonalProjectionOnto_add_smul, LinearIsometryEquiv.symm_apply_apply]
    right_inv w := by
      simp only [LinearIsometryEquiv.apply_symm_apply]
      rw [Submodule.coe_orthogonalProjectionOnto_orthogonal_singleton (norm_eq_of_mem_sphere x),
        sub_add_cancel]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

@[simp]
theorem sphereTangentProdEquiv_apply (x : sphere (0 : E) 1) (p : TangentSpace (𝓡 m) x × ℝ) :
    sphereTangentProdEquiv m x p = (TauCeti.sphereTangentEquiv x p.1 : E) + p.2 • (x : E) :=
  (rfl)

@[simp]
theorem sphereTangentProdEquiv_symm_apply (x : sphere (0 : E) 1) (w : E) :
    (sphereTangentProdEquiv m x).symm w = ((TauCeti.sphereTangentEquiv x).symm
      ((ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto w), ⟪(x : E), w⟫_ℝ) :=
  (rfl)

variable (E m) in
/-- **The tangent bundle of the sphere plus a trivial line is trivial.** The homeomorphism from
the total space of `TS ×ᵇ Trivial S ℝ`, over the unit sphere `S` of `E`, to that of the trivial
bundle `Trivial S E`, which on the fibre over `x` is the linear isomorphism
`sphereTangentProdEquiv m x`, `(v, t) ↦ dι(v) + t • x`. -/
def sphereTangentProdHomeomorph :
    TotalSpace (EuclideanSpace ℝ (Fin m) × ℝ)
        ((TangentSpace (𝓡 m) : sphere (0 : E) 1 → Type) ×ᵇ Trivial (sphere (0 : E) 1) ℝ) ≃ₜ
      TotalSpace E (Trivial (sphere (0 : E) 1) E) :=
  TauCeti.bundleHomeomorph (sphereTangentProdEquiv m) <| by
    simp only [sphereTangentProdEquiv_apply]
    have hdiag := (FiberBundle.Prod.isInducing_diag (EuclideanSpace ℝ (Fin m))
      (TangentSpace (𝓡 m) : sphere (0 : E) 1 → Type) ℝ
      (Trivial (sphere (0 : E) 1) ℝ)).continuous
    have hproj := (FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin m))
      (TangentSpace (𝓡 m) : sphere (0 : E) 1 → Type)).comp (continuous_fst.comp hdiag)
    -- The tangent component `dι(v)`, through the tangent map of the inclusion.
    have hv := (TauCeti.contMDiff_coe_sphereTangentEquiv (E := E) (n := m)
      (m := 0)).continuous.comp (continuous_fst.comp hdiag)
    have ht := continuous_snd.comp
      ((Trivial.isInducing_toProd (sphere (0 : E) 1) ℝ).continuous.comp
        (continuous_snd.comp hdiag))
    exact (Trivial.isInducing_toProd (sphere (0 : E) 1) E).continuous_iff.2
      (hproj.prodMk (hv.add (ht.smul (continuous_subtypeVal.comp hproj))))

@[simp]
theorem proj_sphereTangentProdHomeomorph
    (p : TotalSpace (EuclideanSpace ℝ (Fin m) × ℝ)
      ((TangentSpace (𝓡 m) : sphere (0 : E) 1 → Type) ×ᵇ Trivial (sphere (0 : E) 1) ℝ)) :
    (sphereTangentProdHomeomorph E m p).proj = p.proj :=
  by rw [sphereTangentProdHomeomorph, TauCeti.bundleHomeomorph_apply]

@[simp]
theorem snd_sphereTangentProdHomeomorph
    (p : TotalSpace (EuclideanSpace ℝ (Fin m) × ℝ)
      ((TangentSpace (𝓡 m) : sphere (0 : E) 1 → Type) ×ᵇ Trivial (sphere (0 : E) 1) ℝ)) :
    (sphereTangentProdHomeomorph E m p).snd = sphereTangentProdEquiv m p.proj p.snd :=
  by rw [sphereTangentProdHomeomorph, TauCeti.bundleHomeomorph_apply]

@[simp]
theorem proj_sphereTangentProdHomeomorph_symm (q : TotalSpace E (Trivial (sphere (0 : E) 1) E)) :
    ((sphereTangentProdHomeomorph E m).symm q).proj = q.proj :=
  by rw [sphereTangentProdHomeomorph, TauCeti.bundleHomeomorph_symm_apply]

@[simp]
theorem snd_sphereTangentProdHomeomorph_symm (q : TotalSpace E (Trivial (sphere (0 : E) 1) E)) :
    ((sphereTangentProdHomeomorph E m).symm q).snd =
      (sphereTangentProdEquiv m q.proj).symm q.snd :=
  by rw [sphereTangentProdHomeomorph, TauCeti.bundleHomeomorph_symm_apply]

end SymplecticGeometry
