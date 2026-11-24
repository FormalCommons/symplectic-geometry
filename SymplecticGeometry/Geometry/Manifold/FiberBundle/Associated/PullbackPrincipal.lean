/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Pullback
public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Section
public import TauCeti.Geometry.Manifold.FiberBundle.Pullback.Basic
public import SymplecticGeometry.Geometry.Manifold.FiberBundle.Basic

/-!
# The product `P × F` as the pull-back of `P` to `P ×_G F`

Let `P` be a principal `G`-bundle over `B`, let `G` act on the left on a manifold `F`, and let
`M = P ×_G F` be the associated bundle, with charted total space
`TauCeti.ManifoldTotalSpace F (AssociatedBundle G P F)` and projection `π_M : M → B`. The
pull-back `Q = π_M^* P` is a principal `G`-bundle over `M`, whose fibre over `[x, v]` is the fibre
of `P` through `x`. The map `Φ (x, v) = ([x, v], x)` identifies `P × F` with the total space of `Q`:
the class `[x, v]` and the point `y = x` of its fibre recover `v` as the unique `w` with
`[y, w] = [x, v]`. Under `Φ`, the projection of `Q` becomes the quotient map `q (x, v) = [x, v]`,
and the principal action of `G` on `Q` becomes the diagonal action `(x, v) · g = (x · g, g⁻¹ v)`.

## Main definitions and results

* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph`: the `C^n` diffeomorphism `Φ` from
  `ManifoldTotalSpace G P × F` onto the charted total space of `Q`.
* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_apply` and
  `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_symm_apply`: `Φ` and its inverse on points.
* `TauCeti.AssociatedBundle.proj_pullbackProjDiffeomorph`: `π_Q ∘ Φ = q`, at each point.
* `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_smul`: `Φ` is equivariant for the diagonal
  action on the source and the principal action on the target.
* `TauCeti.AssociatedBundle.pullbackProjSection`: the tautological section `m ↦ m` of the
  bundle `Q ×_G F` over `M`, and `TauCeti.AssociatedBundle.contMDiff_pullbackProjSection`:
  it is `C^n`.
* `TauCeti.AssociatedBundle.sectionFunction_pullbackProjSection_eq_iff` and
  `TauCeti.AssociatedBundle.pullbackProjDiffeomorph_symm_snd_eq_iff`: the second coordinate of
  `Φ⁻¹ (m, y)` is the `w` with `[y, w] = m`.

## Implementation notes

The fibre of `Q` over `Φ (x, v)` is that of `P` over the projection of `[x, v]`, which is the base
point of `x` only up to an equation (`TauCeti.ManifoldTotalSpace.homeomorph` does not unfold), so
`Φ` transports `x` along it. The forward map is smooth by the universal property of the pull-back
(`TauCeti.ManifoldTotalSpace.contMDiff_pullback_iff`). The second coordinate of the inverse is the
equivariant function `TauCeti.AssociatedBundle.sectionFunction` of the tautological section, so it
is smooth by `TauCeti.AssociatedBundle.contMDiff_sectionFunction`; the section itself is smooth
since Tau Ceti's comparison `TauCeti.AssociatedBundle.pullbackHomeomorph` of `Q ×_G F` with the
pull-back of `M` to `M` is smooth (`TauCeti.AssociatedBundle.contMDiff_pullbackHomeomorph_iff`).

From `pullbackProjSection` on, the declarations take `[∀ b, Nonempty (P b)]`. Their statements
need it, not only their proofs: Mathlib's and Tau Ceti's fibre bundle structure on the pull-back
`Q` asks for it, and so does `pullbackEquiv`. A caller supplies it with
`have := FiberBundle.nonempty_fiber G P`, since `G` is nonempty.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience, 1963,
  Chapter I, §5 (associated bundles).
* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.3.
-/

public section

noncomputable section

open Bundle MulOpposite TauCeti
open scoped Manifold ContDiff

namespace TauCeti.AssociatedBundle

variable {n : ℕ∞ω} {𝕜 B G F : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F] [MulAction G F]
  [ContinuousSMul G F]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

/-- The projection `π_M` of the associated bundle, as a `C^n` map. -/
local notation "πM" => ManifoldTotalSpace.projContMDiffMap n F (AssociatedBundle G P F) IB IF

/-- The pull-back `Q = π_M^* P` of `P` to the associated bundle. -/
local notation "Q" => (πM : ManifoldTotalSpace F (AssociatedBundle G P F) → B) *ᵖ P

variable (n IB IF) in
/-- The point `([x, v], x)` of the total space of `Q`, before transport to its charted copy. -/
def pullbackProjMk (x : ManifoldTotalSpace G P × F) : TotalSpace G Q :=
  ⟨ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
    ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
      mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩,
    cast (congrArg P (by simp)) ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd⟩

variable (n IB IF) in
/-- The projection of `([x, v], x)` is the class `[x, v]`. -/
@[simp]
theorem pullbackProjMk_proj (x : ManifoldTotalSpace G P × F) :
    (pullbackProjMk n IB IF x).proj =
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
        ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
          mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩ := (rfl)

variable (n IB IF) in
/-- The image of `([x, v], x)` in the total space of `P` is `x`. -/
@[simp]
theorem lift_pullbackProjMk (x : ManifoldTotalSpace G P × F) :
    Pullback.lift πM (pullbackProjMk n IB IF x) = (ManifoldTotalSpace.homeomorph G P).symm x.1 := by
  refine (Pullback.lift_mk _ _ _).trans ?_
  exact (TotalSpace.mk_cast (by simp) _).trans (TotalSpace.eta _)

variable [∀ b, Nonempty (P b)]

variable (n IB IF) in
/-- The tautological section of the bundle associated with `Q` over `M`: at `m` it is `m`
itself, read in the fibre of `Q ×_G F` over `m` through Tau Ceti's `pullbackEquiv`. -/
def pullbackProjSection (m : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    AssociatedBundle G Q F m :=
  (pullbackEquiv πM m).symm ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm m).snd

variable (n IB IF) in
/-- Read in the fibre of `M` over `π_M m`, the tautological section at `m` is `m`. -/
@[simp]
theorem pullbackEquiv_pullbackProjSection (m : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    pullbackEquiv πM m (pullbackProjSection n IB IF m) =
      ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm m).snd :=
  Equiv.apply_symm_apply _ _

variable (n IB IF) in
/-- The tautological section is `C^n`, as a map into the charted total space of `Q ×_G F`. -/
theorem contMDiff_pullbackProjSection :
    ContMDiff (IB.prod IF) ((IB.prod IF).prod IF) n fun m ↦
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G Q F)
        ⟨m, pullbackProjSection n IB IF m⟩ := by
  rcases isEmpty_or_nonempty F with hF | hF
  · -- With `F` empty, so is `M`.
    intro m
    obtain ⟨-, w, -⟩ :=
      exists_mk ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm m).snd
    exact isEmptyElim w
  refine (contMDiff_pullbackHomeomorph_iff πM).2 <|
    (ManifoldTotalSpace.contMDiff_pullback_iff πM (πM).contMDiff).2
      ⟨contMDiff_id.congr fun m ↦ by simp only [pullbackHomeomorph_apply, id], ?_⟩
  refine contMDiff_id.congr fun m ↦ ?_
  rw [pullbackHomeomorph_apply]
  dsimp only
  rw [pullbackEquiv_pullbackProjSection]
  -- The image in `M` of `⟨m, a⟩` is `⟨π_M m, a⟩` by definition, and `π_M m` is the projection of
  -- the point of `M` that `m` stands for; `Pullback.lift_mk` does not rewrite here.
  exact (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).apply_symm_apply m

/-- The equivariant function of the tautological section takes the value `w` at a point
`z = (m, y)` of the total space of `Q` exactly when `m` is the class `[y, w]`, with `y` read in
the total space of `P`. -/
theorem sectionFunction_pullbackProjSection_eq_iff (z : TotalSpace G Q) (w : F) :
    sectionFunction (pullbackProjSection n IB IF) z = w ↔
      (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm z.proj =
        ⟨(Pullback.lift πM z).proj, mk G (Pullback.lift πM z).snd w⟩ := by
  obtain ⟨m, y⟩ := z
  rw [sectionFunction_eq_iff, ← (pullbackEquiv πM m).injective.eq_iff,
    pullbackEquiv_pullbackProjSection, pullbackEquiv_mk πM m y w]
  have key (t : TotalSpace F (AssociatedBundle G P F)) (a : AssociatedBundle G P F t.proj) :
      a = t.snd ↔ t = ⟨t.proj, a⟩ := by
    rw [eq_comm, ← TotalSpace.mk_inj (b := t.proj)]
  -- The image of `⟨m, y⟩` in `P` is `⟨π_M m, y⟩` by definition, and `π_M m` is the projection
  -- of the point of `M` that `m` stands for; `Pullback.lift_mk` does not rewrite here.
  exact key _ _

variable [LieGroup IG n G] [ContMDiffSMul IG IF n G F]

variable (n IB IG IF) in
/-- **`P × F` is the pull-back of `P` to the associated bundle.** The `C^n` diffeomorphism
`(x, v) ↦ ([x, v], x)` from `P × F` onto the total space of the pull-back `Q = π_M^* P` of `P` to
`M = P ×_G F`. -/
def pullbackProjDiffeomorph :
    (ManifoldTotalSpace G P × F) ≃ₘ^n⟮(IB.prod IG).prod IF, (IB.prod IF).prod IG⟯
      ManifoldTotalSpace G Q where
  toFun x := ManifoldTotalSpace.homeomorph G Q (pullbackProjMk n IB IF x)
  invFun z :=
    (ManifoldTotalSpace.homeomorph G P
        (Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)),
      sectionFunction (pullbackProjSection n IB IF) ((ManifoldTotalSpace.homeomorph G Q).symm z))
  left_inv x := by
    refine Prod.ext ?_ ?_
    · simp [lift_pullbackProjMk]
    · refine (sectionFunction_pullbackProjSection_eq_iff _ _).2 ?_
      rw [Homeomorph.symm_apply_apply, lift_pullbackProjMk, pullbackProjMk_proj,
        Homeomorph.symm_apply_apply]
  right_inv z := by
    obtain ⟨y, rfl⟩ := (ManifoldTotalSpace.homeomorph G Q).surjective z
    simp only [Homeomorph.symm_apply_apply]
    congr 1
    refine Pullback.totalSpace_ext ?_ ?_
    · rw [pullbackProjMk_proj, Homeomorph.symm_apply_apply,
        ← (sectionFunction_pullbackProjSection_eq_iff y _).1 rfl, Homeomorph.apply_symm_apply]
    · rw [lift_pullbackProjMk, Homeomorph.symm_apply_apply]
  contMDiff_toFun := by
    refine (ManifoldTotalSpace.contMDiff_pullback_iff πM (πM).contMDiff).2 ⟨?_, ?_⟩
    · exact contMDiff_totalSpaceMk_mk n G F IB IG IF P
    · simp only [lift_pullbackProjMk, Homeomorph.apply_symm_apply]
      exact contMDiff_fst
  contMDiff_invFun := by
    refine (ManifoldTotalSpace.contMDiff_pullbackLift n IG πM (πM).contMDiff).prodMk ?_
    exact contMDiff_sectionFunction _ (contMDiff_pullbackProjSection n IB IF)

/-- `Φ (x, v)` is the point `([x, v], x)`. -/
theorem pullbackProjDiffeomorph_apply (x : ManifoldTotalSpace G P × F) :
    pullbackProjDiffeomorph n IB IG IF x =
      ManifoldTotalSpace.homeomorph G Q (pullbackProjMk n IB IF x) := (rfl)

/-- The inverse of `Φ` sends `(m, y)` to `(y, w)` with `[y, w] = m`. -/
theorem pullbackProjDiffeomorph_symm_apply (z : ManifoldTotalSpace G Q) :
    (pullbackProjDiffeomorph n IB IG IF).symm z =
      (ManifoldTotalSpace.homeomorph G P
          (Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)),
        sectionFunction (pullbackProjSection n IB IF)
          ((ManifoldTotalSpace.homeomorph G Q).symm z)) := (rfl)

/-- The second coordinate of `Φ⁻¹ z`, for `z = (m, y)`, is `w` exactly when `m` is the class
`[y, w]`, with `y` read in the total space of `P`. -/
theorem pullbackProjDiffeomorph_symm_snd_eq_iff (z : ManifoldTotalSpace G Q) (w : F) :
    ((pullbackProjDiffeomorph n IB IG IF).symm z).2 = w ↔
      (ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm
          ((ManifoldTotalSpace.homeomorph G Q).symm z).proj =
        ⟨(Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)).proj,
          mk G (Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm z)).snd w⟩ := by
  rw [pullbackProjDiffeomorph_symm_apply, sectionFunction_pullbackProjSection_eq_iff]

/-- **The projection of `Q` composed with `Φ` is the quotient map** `(x, v) ↦ [x, v]`. -/
-- Not `@[simp]`: at a point `(homeomorph G P p, v)` it leaves a dependent pair that `simp` cannot
-- reduce, where `proj_pullbackProjDiffeomorph_homeomorph` gives `[p, v]`.
theorem proj_pullbackProjDiffeomorph (x : ManifoldTotalSpace G P × F) :
    ((ManifoldTotalSpace.homeomorph G Q).symm (pullbackProjDiffeomorph n IB IG IF x)).proj =
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)
        ⟨((ManifoldTotalSpace.homeomorph G P).symm x.1).proj,
          mk G ((ManifoldTotalSpace.homeomorph G P).symm x.1).snd x.2⟩ := by
  rw [pullbackProjDiffeomorph_apply, Homeomorph.symm_apply_apply, pullbackProjMk_proj]

/-- The projection of `Φ (p, v)` is the class `[p, v]`, for a point `p` of the total space
of `P`. -/
@[simp]
theorem proj_pullbackProjDiffeomorph_homeomorph (p : TotalSpace G P) (v : F) :
    ((ManifoldTotalSpace.homeomorph G Q).symm
        (pullbackProjDiffeomorph n IB IG IF (ManifoldTotalSpace.homeomorph G P p, v))).proj =
      ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F) ⟨p.proj, mk G p.snd v⟩ := by
  rw [proj_pullbackProjDiffeomorph, Homeomorph.symm_apply_apply]

/-- The image of `Φ (p, v)` in the total space of `P` is `p`. -/
@[simp]
theorem lift_pullbackProjDiffeomorph_homeomorph (p : TotalSpace G P) (v : F) :
    Pullback.lift πM ((ManifoldTotalSpace.homeomorph G Q).symm
        (pullbackProjDiffeomorph n IB IG IF (ManifoldTotalSpace.homeomorph G P p, v))) = p := by
  rw [pullbackProjDiffeomorph_apply, Homeomorph.symm_apply_apply, lift_pullbackProjMk,
    Homeomorph.symm_apply_apply]

/-- **`Φ` is equivariant**, for the diagonal action `(x, v) · g = (x · g, g⁻¹ • v)` on
`P × F` and the principal action on `Q`. -/
theorem pullbackProjDiffeomorph_smul (g : G) (x : ManifoldTotalSpace G P × F) :
    pullbackProjDiffeomorph n IB IG IF (op g • x.1, g⁻¹ • x.2) =
      op g • pullbackProjDiffeomorph n IB IG IF x := by
  rw [pullbackProjDiffeomorph_apply, pullbackProjDiffeomorph_apply,
    ManifoldTotalSpace.smul_homeomorph]
  congr 1
  refine Pullback.totalSpace_ext ?_ ?_
  · rw [pullbackProjMk_proj, pullbackProjMk_proj, ManifoldTotalSpace.homeomorph_symm_smul,
      mk_smul_inv_smul]
  · rw [lift_pullbackProjMk, ManifoldTotalSpace.homeomorph_symm_smul]
    -- `Pullback.lift` of a point `⟨m, s⟩` is `⟨πM m, s⟩` by definition; `Pullback.lift_mk` does not
    -- rewrite here, since the fibre of `Q` is not reducibly that of `P`.
    exact congrArg (fun y : TotalSpace G P ↦ (⟨y.proj, op g • y.snd⟩ : TotalSpace G P))
      (lift_pullbackProjMk n IB IF x).symm

end TauCeti.AssociatedBundle
