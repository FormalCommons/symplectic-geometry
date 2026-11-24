/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.ComplexCoefficients
public import SymplecticGeometry.Geometry.Manifold.DeRham.Hodge.Complex
public import SymplecticGeometry.Geometry.Manifold.DeRham.Kahler.Identities
public import TauCeti.Geometry.Hodge.Decomposition
public import TauCeti.Geometry.Hodge.Dimension
import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.AlmostComplexType

/-!
# The Hodge decomposition of complex de Rham cohomology

Let `J` be a smooth almost complex structure on a manifold `M`. The subspace
`H^{p,q}` of complex de Rham cohomology `H^k_dR(M; ℂ)` is the space of classes of closed complex
forms of type `(p,q)` for `J`, `TauCeti.complexDeRhamCohomology.hodgePiece J k p q`. Complex
conjugation exchanges `H^{p,q}` and `H^{q,p}`.

Now let `M` be compact and boundaryless, `J` integrable, `σ` a closed two-form, and let the
metric be `⟪v, w⟫ = σ(v, J w)`, as on a closed Kähler manifold. Since the Hodge Laplacian commutes
with the derivation of `J` (`TauCeti.SmoothForm.hodgeLaplacian_realAlternatingDerivation`), its
complexification preserves the type of forms and commutes with the type projections, so the type
components of a harmonic form are harmonic. Every closed form of type `(p,q)` is cohomologous to the
type-`(p,q)` component of its harmonic part, because a closed Laplacian is exact. Hence `H^{p,q}`
is the image of the harmonic forms of type `(p,q)`, and since harmonic forms map isomorphically
onto cohomology, the spaces `H^{p,q}`, `p + q = k`, form a Hodge decomposition of weight `k` of
`H^k_dR(M; ℂ)`.

The results hold for every orientation of `M`: harmonic forms, and so the pieces, do not depend
on it. In particular they hold for the symplectic orientation of a Kähler form.

## Main definitions

* `TauCeti.complexDeRhamCohomology.hodgePiece J k p q`: the classes of closed forms of type
  `(p,q)`.
* `TauCeti.complexDeRhamCohomology.kahlerHodgeStructure`: the Hodge structure of weight `k` on
  `H^k_dR(M; ℂ)` that the decomposition generates.

## Main results

* `TauCeti.complexDeRhamCohomology.mem_hodgePiece_iff`,
  `TauCeti.complexDeRhamCohomology.hodgePiece_eq_bot`: membership, and vanishing unless
  `p + q = k`.
* `TauCeti.complexDeRhamCohomology.map_conj_hodgePiece`: conjugation exchanges `H^{p,q}` and
  `H^{q,p}`.
* `TauCeti.SmoothForm.complexHodgeStar_alternatingDerivation`: the complex Hodge star commutes
  with the derivation of an endomorphism field that is skew-adjoint at every point.
* `TauCeti.SmoothForm.IsOfType.complexHodgeStar`: in dimension `2 n`, with `J` orthogonal, the
  Hodge star of a form of type `(p,q)`, `p, q ≤ n`, has type `(n - q, n - p)`.
* `TauCeti.SmoothAlmostComplexStructure.typeProjection_complexHodgeLaplacian` and
  `TauCeti.SmoothAlmostComplexStructure.typeProjection_mem_complexHarmonicForms`: the type
  projections commute with the complex Hodge Laplacian and preserve harmonic forms.
* `TauCeti.complexDeRhamCohomology.hodgePiece_eq_map_complexHarmonicForms`: `H^{p,q}` is the image
  of the harmonic forms of type `(p,q)`.
* `TauCeti.complexDeRhamCohomology.isHodgeDecomposition_hodgePiece`: the Hodge decomposition.

## References

* [P. Griffiths, J. Harris, *Principles of Algebraic Geometry*][GriffithsHarris1978],
  Chapter 0, §7.
* [J.-P. Demailly, *Complex Analytic and Differential Geometry*][Demailly2012],
  Chapter VI, Theorem (8.5).
* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  (4.3.8).
-/

public section

noncomputable section

open Bundle Module SymplecticGeometry
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The pieces `H^{p,q}` and conjugation -/

namespace complexDeRhamCohomology

variable (J : SmoothAlmostComplexStructure I M) {k p q : ℕ}

/-- The subspace `H^{p,q}` of complex de Rham cohomology `H^k_dR(M; ℂ)` for an almost complex
structure `J`: the classes of closed complex `k`-forms in the range of the type-`(p,q)`
projection, that is, of type `(p,q)` (`mem_hodgePiece_iff`). It is `⊥` unless `p + q = k`
(`hodgePiece_eq_bot`). -/
def hodgePiece (k p q : ℕ) : Submodule ℂ (complexDeRhamCohomology I M k) :=
  ((LinearMap.range (J.typeProjection (F := ℂ) (k := k) p q)).comap
    (complexClosedForms I M k).subtype).map (mk I k)

/-- `H^{p,q}` is the image under `mk` of the closed forms in the range of the type projection. -/
theorem hodgePiece_def (k p q : ℕ) :
    hodgePiece J k p q =
      ((LinearMap.range (J.typeProjection (F := ℂ) (k := k) p q)).comap
        (complexClosedForms I M k).subtype).map (mk I k) :=
  (rfl)

/-- For `p + q = k`, the classes in `H^{p,q}` are those of the closed forms of type `(p,q)`. -/
theorem mem_hodgePiece_iff (hpq : p + q = k) (c : complexDeRhamCohomology I M k) :
    c ∈ hodgePiece J k p q ↔
      ∃ φ : complexClosedForms I M k, φ.val.IsOfType J p q ∧ mk I k φ = c := by
  simp only [hodgePiece_def, Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
    J.mem_range_typeProjection_iff hpq]

/-- The class of a closed form of type `(p,q)` lies in `H^{p,q}`. -/
theorem mk_mem_hodgePiece {φ : complexClosedForms I M k} (hφ : φ.val.IsOfType J p q) :
    mk I k φ ∈ hodgePiece J k p q :=
  (mem_hodgePiece_iff J hφ.add_eq _).2 ⟨φ, hφ, rfl⟩

/-- `H^{p,q}` vanishes in degree `k ≠ p + q`. -/
theorem hodgePiece_eq_bot (hpq : p + q ≠ k) : hodgePiece J k p q = ⊥ := by
  simp [hodgePiece_def, J.typeProjection_eq_zero hpq]

/-- With the indexing of a Hodge decomposition by `p : ℤ`, the pieces of index `p < 0` or
`p > k` vanish. -/
theorem hodgePiece_toNat_eq_bot {p : ℤ} (hp : p < 0 ∨ k < p) :
    hodgePiece J k p.toNat ((k : ℤ) - p).toNat = ⊥ :=
  hodgePiece_eq_bot J (by omega)

/-- Complex conjugation maps `H^{p,q}` into `H^{q,p}`. -/
theorem conj_mem_hodgePiece {c : complexDeRhamCohomology I M k} (hc : c ∈ hodgePiece J k p q) :
    (conj k).toEquiv c ∈ hodgePiece J k q p := by
  obtain ⟨φ, ⟨ψ, hψ⟩, rfl⟩ := hc
  rw [Submodule.coe_subtype] at hψ
  rw [conj_mk]
  refine ⟨complexClosedForms.conj I φ, ⟨SmoothForm.mapCoeff (Complex.conjCLE : ℂ →L[ℝ] ℂ) ψ, ?_⟩,
    rfl⟩
  rw [Submodule.coe_subtype, complexClosedForms.coe_conj, ← hψ,
    J.mapCoeff_typeProjection_of_map_smul_conj (fun c v ↦ by simp)]

/-- **Hodge symmetry in cohomology**: complex conjugation maps `H^{p,q}` onto `H^{q,p}`. -/
theorem map_conj_hodgePiece (p q : ℕ) :
    (hodgePiece J k p q).map (conj k).toEquiv.toLinearMap = hodgePiece J k q p := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun c hc ↦ conj_mem_hodgePiece J hc)
    fun c hc ↦ ⟨(conj k).toEquiv c, conj_mem_hodgePiece J hc, ?_⟩
  rw [LinearEquiv.coe_toLinearMap, Hodge.Conjugation.apply_apply]

end complexDeRhamCohomology

/-! ### The Laplacian, the Hodge star and types of forms -/

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] {m k l : ℕ}
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

namespace SmoothForm

/-- Under the hypotheses of `hodgeLaplacian_realAlternatingDerivation`, the complex Hodge
Laplacian commutes with the derivation `J.toEndomorphism.alternatingDerivation` of complex
forms. -/
theorem complexHodgeLaplacian_alternatingDerivation (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) (φ : SmoothForm I M ℂ k) :
    complexHodgeLaplacian o hkl (J.toEndomorphism.alternatingDerivation φ) =
      J.toEndomorphism.alternatingDerivation (complexHodgeLaplacian o hkl φ) := by
  rw [complexHodgeLaplacian_def,
    complexifyₗ_alternatingDerivation _ (hodgeLaplacian_realAlternatingDerivation o hJ hσ hg hkl)]

/-- Under the hypotheses of `hodgeLaplacian_realAlternatingDerivation`, the complex Hodge
Laplacian of a form of type `(p,q)` has type `(p,q)`. -/
theorem IsOfType.complexHodgeLaplacian {p q : ℕ} (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) {φ : SmoothForm I M ℂ k} (hφ : φ.IsOfType J p q) :
    (complexHodgeLaplacian o hkl φ).IsOfType J p q :=
  isOfType_iff.2
    ⟨hφ.add_eq, by
      rw [← complexHodgeLaplacian_alternatingDerivation o hJ hσ hg, (isOfType_iff.1 hφ).2,
        map_smul]⟩

/-- On an oriented manifold with a smooth metric, the complex Hodge star commutes with the
derivation `A.alternatingDerivation` of complex forms, for an endomorphism field `A` that is
skew-adjoint at every point. -/
theorem complexHodgeStar_alternatingDerivation (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m)
    {A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x}
    (hA : ∀ x (u w : TangentSpace I x), ⟪A x u, w⟫ = -⟪u, A x w⟫) (φ : SmoothForm I M ℂ k) :
    complexHodgeStar o hkl (A.alternatingDerivation φ) =
      A.alternatingDerivation (complexHodgeStar o hkl φ) := by
  rw [complexHodgeStar_def,
    complexifyₗ_alternatingDerivation _ (hodgeStar_realAlternatingDerivation o hkl hA)]

/-- On an oriented manifold of dimension `2 n` with a metric in which `J` is orthogonal, the
complex Hodge star of a complex form of type `(p,q)`, with `p ≤ n` and `q ≤ n`, has type
`(n - q, n - p)`. -/
theorem IsOfType.complexHodgeStar {n p q : ℕ}
    (o : Manifold.Orientation I M (Fin (2 * n))) (hkl : k + l = 2 * n)
    (hJ : ∀ x (u w : TangentSpace I x), ⟪J x u, w⟫ = -⟪u, J x w⟫) (hp : p ≤ n) (hq : q ≤ n)
    {φ : SmoothForm I M ℂ k} (hφ : φ.IsOfType J p q) :
    (complexHodgeStar o hkl φ).IsOfType J (n - q) (n - p) := by
  have hpq := hφ.add_eq
  refine isOfType_iff.2 ⟨by omega, ?_⟩
  rw [← SmoothForm.complexHodgeStar_alternatingDerivation o hkl hJ, (isOfType_iff.1 hφ).2,
    map_smul, Nat.cast_sub hp, Nat.cast_sub hq, sub_sub_sub_cancel_left]

end SmoothForm

namespace SmoothAlmostComplexStructure

/-- **The type projections commute with the Laplacian**: let `J` be integrable, `σ` a closed
two-form, and the metric `⟪v, w⟫ = σ(v, J w)`. Then on complex `k`-forms, each type projection
commutes with the complex Hodge Laplacian. -/
theorem typeProjection_complexHodgeLaplacian (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) (p q : ℕ) (φ : SmoothForm I M ℂ k) :
    J.typeProjection p q (SmoothForm.complexHodgeLaplacian o hkl φ) =
      SmoothForm.complexHodgeLaplacian o hkl (J.typeProjection p q φ) := by
  -- The type projection is a polynomial in the derivation of `J`, which commutes with `Δ`.
  have h : Commute (SmoothForm.complexHodgeLaplacian o hkl)
      J.toEndomorphism.alternatingDerivation :=
    LinearMap.ext fun ψ ↦ by
      rw [mul_apply_eq_comp, mul_apply_eq_comp,
        SmoothForm.complexHodgeLaplacian_alternatingDerivation o hJ hσ hg hkl]
  have hP := (Algebra.commute_of_mem_adjoin_singleton_of_commute
    (Polynomial.aeval_mem_adjoin_singleton ℂ _ (p := ContinuousLinearMap.typePolynomial k p q))
    h).symm
  rw [← typeProjection_eq_aeval] at hP
  rw [← mul_apply_eq_comp, hP.eq, mul_apply_eq_comp]

/-- Under the hypotheses of `typeProjection_complexHodgeLaplacian`, the type components of a
complex harmonic form are harmonic. -/
theorem typeProjection_mem_complexHarmonicForms (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) (p q : ℕ) {φ : SmoothForm I M ℂ k} (hφ : φ ∈ complexHarmonicForms o hkl) :
    J.typeProjection p q φ ∈ complexHarmonicForms o hkl := by
  rw [mem_complexHarmonicForms_iff] at hφ ⊢
  rw [← typeProjection_complexHodgeLaplacian o hJ hσ hg, hφ, map_zero]

end SmoothAlmostComplexStructure

/-! ### The Hodge decomposition -/

namespace complexDeRhamCohomology

variable [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

/-- **`H^{p,q}` through harmonic forms**: on a compact boundaryless manifold, with `J` integrable,
`σ` a closed two-form and the metric `⟪v, w⟫ = σ(v, J w)`, the subspace `H^{p,q}` of
`H^k_dR(M; ℂ)` is the image of the complex harmonic forms in the range of the type-`(p,q)`
projection. -/
theorem hodgePiece_eq_map_complexHarmonicForms (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) (p q : ℕ) :
    hodgePiece J k p q =
      ((LinearMap.range (J.typeProjection (F := ℂ) (k := k) p q)).comap
        (complexHarmonicForms o hkl).subtype).map
          (complexHarmonicForms.toComplexDeRhamCohomology o hkl) := by
  ext c
  constructor
  · -- A closed form `φ` of type `(p,q)` is `h + Δγ`; then `φ = Π h + Δ (Π γ)`, and `Δ (Π γ)`,
    -- being closed, is exact.
    rintro ⟨φ, ⟨ψ, hψ⟩, rfl⟩
    rw [Submodule.coe_subtype] at hψ
    obtain ⟨h, hh, γ, hγ⟩ := exists_mem_complexHarmonicForms_add_complexHodgeLaplacian o hkl φ.val
    have hph := J.typeProjection_mem_complexHarmonicForms o hJ hσ hg hkl p q hh
    have hφ : φ.val - J.typeProjection p q h =
        SmoothForm.complexHodgeLaplacian o hkl (J.typeProjection p q γ) := by
      rw [← J.typeProjection_complexHodgeLaplacian o hJ hσ hg, sub_eq_iff_eq_add',
        ← map_add, ← hγ, ← hψ, SmoothAlmostComplexStructure.typeProjection_typeProjection,
        ite_eq_left rfl]
    refine ⟨⟨_, hph⟩, ⟨h, rfl⟩, ?_⟩
    rw [complexHarmonicForms.toComplexDeRhamCohomology_apply, eq_comm,
      complexDeRhamCohomology.mk_eq_mk_iff, hφ]
    refine mem_complexExactForms_of_complexHodgeLaplacian_mem_complexClosedForms o hkl ?_
    rw [← hφ]
    exact sub_mem φ.property (complexHarmonicForms_le_complexClosedForms o hkl hph)
  · rintro ⟨h, hh, rfl⟩
    exact ⟨_, hh, (complexHarmonicForms.toComplexDeRhamCohomology_apply o hkl h).symm⟩

/-- The projection of `H^k_dR(M; ℂ)` onto `H^{p,q}` along the other pieces: the type projection
of harmonic representatives. -/
private def typeProjectionCohomology (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) (p q : ℕ) : Module.End ℂ (complexDeRhamCohomology I M k) :=
  (complexHarmonicForms.complexDeRhamCohomologyEquiv o hkl).conj
    ((J.typeProjection p q).restrict
      fun _ hφ ↦ J.typeProjection_mem_complexHarmonicForms o hJ hσ hg hkl p q hφ)

private theorem typeProjectionCohomology_toComplexDeRhamCohomology
    (o : Manifold.Orientation I M (Fin m)) (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) (p q : ℕ) (h : complexHarmonicForms o hkl) :
    typeProjectionCohomology o hJ hσ hg hkl p q
        (complexHarmonicForms.toComplexDeRhamCohomology o hkl h) =
      complexHarmonicForms.toComplexDeRhamCohomology o hkl
        ⟨J.typeProjection p q h.val,
          J.typeProjection_mem_complexHarmonicForms o hJ hσ hg hkl p q h.property⟩ := by
  rw [← complexHarmonicForms.complexDeRhamCohomologyEquiv_apply, typeProjectionCohomology,
    LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, LinearMap.restrict_apply,
    complexHarmonicForms.complexDeRhamCohomologyEquiv_apply]

private theorem typeProjectionCohomology_of_mem
    (o : Manifold.Orientation I M (Fin m)) (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) {p q p' q' : ℕ} {c : complexDeRhamCohomology I M k}
    (hc : c ∈ hodgePiece J k p' q') :
    typeProjectionCohomology o hJ hσ hg hkl p q c = if (p, q) = (p', q') then c else 0 := by
  rw [hodgePiece_eq_map_complexHarmonicForms o hJ hσ hg hkl] at hc
  obtain ⟨h, ⟨ψ, hψ⟩, rfl⟩ := hc
  rw [Submodule.coe_subtype] at hψ
  rw [typeProjectionCohomology_toComplexDeRhamCohomology]
  split_ifs with hpq
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpq
    congr 1
    refine Subtype.ext ?_
    dsimp only
    rw [← hψ, SmoothAlmostComplexStructure.typeProjection_typeProjection, ite_eq_left rfl]
  · rw [← map_zero (complexHarmonicForms.toComplexDeRhamCohomology o hkl)]
    congr 1
    refine Subtype.ext ?_
    dsimp only
    rw [← hψ, SmoothAlmostComplexStructure.typeProjection_typeProjection, ite_eq_right hpq,
      ZeroMemClass.coe_zero]

private theorem typeProjectionCohomology_mem
    (o : Manifold.Orientation I M (Fin m)) (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) (p q : ℕ) (c : complexDeRhamCohomology I M k) :
    typeProjectionCohomology o hJ hσ hg hkl p q c ∈ hodgePiece J k p q := by
  obtain ⟨h, rfl⟩ := (complexHarmonicForms.toComplexDeRhamCohomology_bijective o hkl).2 c
  rw [typeProjectionCohomology_toComplexDeRhamCohomology,
    hodgePiece_eq_map_complexHarmonicForms o hJ hσ hg hkl]
  exact ⟨_, ⟨h.val, rfl⟩, rfl⟩

private theorem sum_typeProjectionCohomology
    (o : Manifold.Orientation I M (Fin m)) (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) (c : complexDeRhamCohomology I M k) :
    ∑ pq ∈ Finset.antidiagonal k, typeProjectionCohomology o hJ hσ hg hkl pq.1 pq.2 c = c := by
  obtain ⟨h, rfl⟩ := (complexHarmonicForms.toComplexDeRhamCohomology_bijective o hkl).2 c
  simp only [typeProjectionCohomology_toComplexDeRhamCohomology, ← map_sum]
  congr 1
  rw [Subtype.ext_iff, Submodule.coe_sum, SmoothAlmostComplexStructure.sum_typeProjection]

/-- **The Hodge decomposition**: on a compact boundaryless manifold of dimension `m` with an
integrable almost complex structure `J`, a closed two-form `σ`, a metric `⟪v, w⟫ = σ(v, J w)` and
an orientation, the subspaces `H^{p,k-p}`, indexed by `p : ℤ` (and `⊥` for `p < 0` or `p > k`),
form a Hodge decomposition of weight `k` of `H^k_dR(M; ℂ)` for complex conjugation: an internal
direct sum, exchanged by conjugation in complementary bidegrees. -/
theorem isHodgeDecomposition_hodgePiece (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) :
    Hodge.IsHodgeDecomposition (conj k) k
      (fun p : ℤ ↦ hodgePiece J k p.toNat (k - p).toNat) where
  isInternal := by
    refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (fun i ↦ ?_) ?_
    · rw [Submodule.disjoint_def]
      intro c hci hc
      by_cases hi : 0 ≤ i ∧ i ≤ k
      · -- The projection onto the piece of index `i` fixes `c` and kills the other pieces.
        have hP := typeProjectionCohomology_of_mem o hJ hσ hg hkl (p := i.toNat)
          (q := ((k : ℤ) - i).toNat) hci
        rw [ite_eq_left rfl] at hP
        rw [← hP]
        refine (iSup₂_le fun j hj ↦ ?_ : _ ≤ LinearMap.ker
          (typeProjectionCohomology o hJ hσ hg hkl i.toNat ((k : ℤ) - i).toNat)) hc
        intro d hd
        rw [LinearMap.mem_ker, typeProjectionCohomology_of_mem o hJ hσ hg hkl hd, ite_eq_right]
        rw [Prod.mk.injEq]
        omega
      · rw [hodgePiece_toNat_eq_bot J (by omega)] at hci
        exact (Submodule.mem_bot ℂ).1 hci
    · refine eq_top_iff.2 fun c _ ↦ ?_
      rw [← sum_typeProjectionCohomology o hJ hσ hg hkl c]
      refine Submodule.sum_mem _ fun pq hpq ↦ Submodule.mem_iSup_of_mem (pq.1 : ℤ) ?_
      rw [Finset.mem_antidiagonal] at hpq
      have h₁ : (pq.1 : ℤ).toNat = pq.1 := Int.toNat_natCast _
      have h₂ : ((k : ℤ) - pq.1).toNat = pq.2 := by omega
      rw [h₁, h₂]
      exact typeProjectionCohomology_mem o hJ hσ hg hkl _ _ c
  map_conj p := by
    rw [map_conj_hodgePiece, sub_sub_cancel]
  exists_forall_lt_eq_bot := ⟨0, fun p hp ↦ hodgePiece_toNat_eq_bot J (Or.inl hp)⟩

/-- The pure Hodge structure of weight `k` on `H^k_dR(M; ℂ)` generated by the Hodge decomposition
`isHodgeDecomposition_hodgePiece`. -/
def kahlerHodgeStructure (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) : Hodge.HodgeStructureOn (complexDeRhamCohomology I M k) (conj k) k :=
  Hodge.HodgeStructureOn.ofDecomposition (isHodgeDecomposition_hodgePiece o hJ hσ hg hkl)

/-- The Hodge components of `kahlerHodgeStructure` are the pieces `H^{p,k-p}`. -/
@[simp]
theorem kahlerHodgeStructure_piece (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) (p : ℤ) :
    (kahlerHodgeStructure o hJ hσ hg hkl).piece p = hodgePiece J k p.toNat (k - p).toNat :=
  Hodge.HodgeStructureOn.ofDecomposition_piece _ p

/-- The Hodge number `h^{p,k-p}` of `kahlerHodgeStructure`, for `p : ℕ`, is the dimension of
`H^{p,k-p}` (both vanish for `p > k`). -/
theorem hodgeNumber_kahlerHodgeStructure (o : Manifold.Orientation I M (Fin m))
    (hJ : J.IsIntegrable) (hσ : σ.IsClosed)
    (hg : ∀ x (v w : TangentSpace I x), ⟪v, w⟫ = σ.eval₂ x v (J x w))
    (hkl : k + l = m) (p : ℕ) :
    (kahlerHodgeStructure o hJ hσ hg hkl).hodgeNumber p = finrank ℂ (hodgePiece J k p (k - p)) := by
  rw [Hodge.HodgeStructureOn.hodgeNumber_def, kahlerHodgeStructure_piece, Int.toNat_natCast,
    Int.toNat_sub', Int.toNat_natCast]

end complexDeRhamCohomology

end TauCeti

end
