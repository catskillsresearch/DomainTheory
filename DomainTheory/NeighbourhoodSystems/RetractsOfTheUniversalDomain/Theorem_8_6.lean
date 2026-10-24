module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_24
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition_6_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_13

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Examples_8_4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition_8_7
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_9
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem_7_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}
/- concordance: source L4890 THEOREM 8.6 sub combinator -/
/-- **Theorem 8.6's combinator `sub(f)` (Scott 1981, PRG-19), per token `f`.** Scott's formula
`X sub(f) Z ↔ ∃Y ∈ E, X⊆Y ∧ f.rel Y Y ∧ Y⊆Z` is literally `retractionOfSubsystem` applied to
`fixedNbhd f = {Y ∈ E ∣ Y f Y}` (Theorem 8.5's subsystem, built for *any* `f`). -/
def sub (f : ApproximableMap E E) : ApproximableMap E E :=
  Subsystem.retractionOfSubsystem (fixedNbhd_subsystem f)
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

@[simp] theorem sub_rel {f : ApproximableMap E E} {X Z : Set α} :
    (sub f).rel X Z ↔ E.mem X ∧ E.mem Z ∧ ∃ Y, (E.mem Y ∧ f.rel Y Y) ∧ X ⊆ Y ∧ Y ⊆ Z :=
  Subsystem.retractionOfSubsystem_rel (fixedNbhd_subsystem f)
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- `fixedNbhd (retractionOfSubsystem h) = D`: the round trip recovering a subsystem `D` from the
retraction it induces. `Y (retractionOfSubsystem h) Y ↔ ∃W∈D, Y⊆W⊆Y`, and `Y⊆W⊆Y` forces `W=Y`, so
this says exactly `D.mem Y` (using `E.mem Y` for free from `D ⊆ E`). -/
theorem fixedNbhd_retractionOfSubsystem {D : NeighborhoodSystem α} (h : D ◁ E) :
    fixedNbhd (Subsystem.retractionOfSubsystem h) = D := by
  apply NeighborhoodSystem.ext
  · intro X
    rw [fixedNbhd_mem, Subsystem.retractionOfSubsystem_rel]
    constructor
    · rintro ⟨hXE, -, -, Y, hY, hXY, hYX⟩
      rw [Set.Subset.antisymm hXY hYX]
      exact hY
    · intro hX
      exact ⟨h.sub hX, h.sub hX, h.sub hX, X, hX, subset_rfl, subset_rfl⟩
  · exact h.master_eq.symm
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`sub`, transported to the function space's own `Element` type via `funSpaceEquiv`.** -/
def subFilter (φ : (funSpace E E).Element) : (funSpace E E).Element :=
  toFilter (sub (toApproxMap φ))

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **`sub` is monotone.** `f ≤ g → sub f ≤ sub g`: immediate from `fixedNbhd`'s definition, since
`f.rel Y Y → g.rel Y Y` whenever `f ≤ g`. -/
theorem sub_mono {f g : ApproximableMap E E} (h : f ≤ g) : sub f ≤ sub g := by
  rintro X Z hr
  obtain ⟨hX, hZ, Y, ⟨hYE, hYf⟩, hXY, hYZ⟩ := sub_rel.mp hr
  exact sub_rel.mpr ⟨hX, hZ, Y, ⟨hYE, h Y Y hYf⟩, hXY, hYZ⟩
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- Every `retractionOfSubsystem h` is already a fixed point of `sub` — immediate from the round
trip `fixedNbhd_retractionOfSubsystem`, since `sub` is *defined* as `retractionOfSubsystem` applied
to `fixedNbhd`. -/
theorem sub_retractionOfSubsystem {D : NeighborhoodSystem α} (h : D ◁ E) :
    sub (Subsystem.retractionOfSubsystem h) = Subsystem.retractionOfSubsystem h := by
  unfold sub
  congr 1
  exact fixedNbhd_retractionOfSubsystem h
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **The finitary projections on `E` are order-isomorphic to the subsystems of `E`.** Forward:
`f ↦ ⟨fixedNbhd f, fixedNbhd_subsystem f⟩`; backward: `D ↦ retractionOfSubsystem D` (a fixed point
of `sub`, by `sub_retractionOfSubsystem`). Round trips are `fixedNbhd_retractionOfSubsystem` and
(definitionally) `sub`'s own defining equation; order is preserved/reflected via `sub`'s formula
being monotone in the underlying subsystem (`retractionOfSubsystem_rel`'s witness clause) together
with `Subsystem.subsystem_iff_subset_of_common`. -/
def finitaryProjectionSubsystemEquiv (E : NeighborhoodSystem α) :
    {f : ApproximableMap E E // sub f = f} ≃o {D : NeighborhoodSystem α // D ◁ E} where
  toFun f := ⟨fixedNbhd f.1, fixedNbhd_subsystem f.1⟩
  invFun D := ⟨Subsystem.retractionOfSubsystem D.2, sub_retractionOfSubsystem D.2⟩
  left_inv f := Subtype.ext f.2
  right_inv D := Subtype.ext (fixedNbhd_retractionOfSubsystem D.2)
  map_rel_iff' := by
    intro f g
    constructor
    · intro hle
      have hleD : fixedNbhd f.1 ◁ fixedNbhd g.1 := hle
      have hsub : sub f.1 ≤ sub g.1 := by
        rintro X Z hXZ
        rw [sub_rel] at hXZ ⊢
        obtain ⟨hX, hZ, Y, hY, hXY, hYZ⟩ := hXZ
        exact ⟨hX, hZ, Y, hleD.sub hY, hXY, hYZ⟩
      rwa [f.2, g.2] at hsub
    · intro hfg
      show fixedNbhd f.1 ◁ fixedNbhd g.1
      refine (Subsystem.subsystem_iff_subset_of_common
        (fixedNbhd_subsystem f.1) (fixedNbhd_subsystem g.1)).mpr ?_
      intro X hX
      exact ⟨hX.1, hfg X X hX.2⟩
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem toApproxMap_monotone {φ ψ : (funSpace E E).Element} (h : φ ≤ ψ) :
    toApproxMap φ ≤ toApproxMap ψ := by
  have := (funSpaceEquiv E E).monotone h
  simpa using this

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem subFilter_mono {φ ψ : (funSpace E E).Element} (h : φ ≤ ψ) : subFilter φ ≤ subFilter ψ :=
  toFilter_le_iff.mpr (sub_mono (toApproxMap_monotone h))

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem subFilter_monotone : Monotone (subFilter (E := E)) := fun _ _ h => subFilter_mono h

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- Directed unions of filters correspond, under `toApproxMap`, to the raw (pointwise) union of the
underlying maps' relations — immediate from `mem_iSupDirected` unfolded through `toApproxMap_rel`.
No consistency/directedness argument is needed for this direction. -/
theorem toApproxMap_rel_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k) {X Z : Set α} :
    (toApproxMap (iSupDirected φ hdir)).rel X Z ↔ ∃ i, (toApproxMap (φ i)).rel X Z := by
  simp only [toApproxMap_rel, mem_iSupDirected]

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`sub` commutes with directed unions of relations.** `sub`'s formula (`sub_rel`) is a positive
existential in `f`'s relation (`∃Y, ... ∧ f.rel Y Y ∧ ...`), so it commutes with an arbitrary union
of relations by pure logic (swapping the order of two existentials) — no directedness needed here
either, only for `iSupDirected` to be well-formed in the first place. -/
theorem sub_toApproxMap_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k) {X Z : Set α} :
    (sub (toApproxMap (iSupDirected φ hdir))).rel X Z ↔
      ∃ i, (sub (toApproxMap (φ i))).rel X Z := by
  simp only [sub_rel, toApproxMap_rel_iSupDirected]
  constructor
  · rintro ⟨hX, hZ, Y, ⟨hYE, i, hYi⟩, hXY, hYZ⟩
    exact ⟨i, hX, hZ, Y, ⟨hYE, hYi⟩, hXY, hYZ⟩
  · rintro ⟨i, hX, hZ, Y, ⟨hYE, hYi⟩, hXY, hYZ⟩
    exact ⟨hX, hZ, Y, ⟨hYE, i, hYi⟩, hXY, hYZ⟩

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem toApproxMap_toFilter (f : ApproximableMap E E) : toApproxMap (toFilter f) = f :=
  (funSpaceEquiv E E).right_inv f

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem toApproxMap_subFilter (φ : (funSpace E E).Element) :
    toApproxMap (subFilter φ) = sub (toApproxMap φ) :=
  toApproxMap_toFilter _

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem toFilter_toApproxMap (φ : (funSpace E E).Element) : toFilter (toApproxMap φ) = φ :=
  (funSpaceEquiv E E).left_inv φ

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem toApproxMap_injective {φ ψ : (funSpace E E).Element} (h : toApproxMap φ = toApproxMap ψ) :
    φ = ψ := by
  rw [← toFilter_toApproxMap φ, ← toFilter_toApproxMap ψ, h]

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`subFilter` preserves directed unions.** Assembled from `sub_toApproxMap_iSupDirected` and
`toApproxMap_rel_iSupDirected` via `toApproxMap`'s injectivity. -/
theorem subFilter_iSupDirected {I : Type u} [Nonempty I] (φ : I → (funSpace E E).Element)
    (hdir : ∀ i j, ∃ k, φ i ≤ φ k ∧ φ j ≤ φ k)
    (hdir' : ∀ i j, ∃ k, subFilter (φ i) ≤ subFilter (φ k) ∧ subFilter (φ j) ≤ subFilter (φ k)) :
    subFilter (iSupDirected φ hdir) = iSupDirected (fun i => subFilter (φ i)) hdir' := by
  apply toApproxMap_injective
  rw [toApproxMap_subFilter]
  apply ApproximableMap.ext
  intro X Z
  rw [sub_toApproxMap_iSupDirected, toApproxMap_rel_iSupDirected]
  simp only [toApproxMap_subFilter]

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`subFilter` is (topologically) continuous**, via the domain-theoretic bridge
`continuous_of_monotone_iSupDirected` (monotone + preserves directed unions). -/
theorem continuous_subFilter : Continuous (subFilter (E := E)) :=
  continuous_of_monotone_iSupDirected subFilter_monotone subFilter_iSupDirected

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`sub`, packaged as a genuine approximable map on the function space `(E → E)`** (Scott's
remark that `f ↦ sub(f)` is itself approximable), via Exercise 2.13's `ofContinuous`. -/
def subApprox : ApproximableMap (funSpace E E) (funSpace E E) :=
  ofContinuous subFilter continuous_subFilter

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

theorem toElementMap_subApprox (φ : (funSpace E E).Element) :
    subApprox.toElementMap φ = subFilter φ :=
  toElementMap_ofContinuous subFilter continuous_subFilter φ

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6

/-- **`Fix(subApprox) ≃o {f ∣ sub f = f}`.** `subApprox.toElementMap φ = φ` unfolds (via
`toElementMap_subApprox`/`subFilter`) to `toFilter (sub (toApproxMap φ)) = φ`, i.e. exactly
`sub (toApproxMap φ) = toApproxMap φ` after transporting through `toApproxMap`/`toFilter`'s round
trips. -/
def subApproxFixIso :
    {φ : (funSpace E E).Element // subApprox.toElementMap φ = φ} ≃o
      {f : ApproximableMap E E // sub f = f} where
  toFun φ := ⟨toApproxMap φ.1, by
    have h1 : subFilter φ.1 = φ.1 := (toElementMap_subApprox φ.1).symm.trans φ.2
    have h2 : toApproxMap (subFilter φ.1) = toApproxMap φ.1 := congrArg toApproxMap h1
    rwa [toApproxMap_subFilter] at h2⟩
  invFun f := ⟨toFilter f.1, by
    rw [toElementMap_subApprox]
    show subFilter (toFilter f.1) = toFilter f.1
    unfold subFilter
    rw [toApproxMap_toFilter, f.2]⟩
  left_inv φ := Subtype.ext (toFilter_toApproxMap φ.1)
  right_inv f := Subtype.ext (toApproxMap_toFilter f.1)
  map_rel_iff' := by
    intro φ ψ
    show toApproxMap φ.1 ≤ toApproxMap ψ.1 ↔ φ.1 ≤ ψ.1
    exact (funSpaceEquiv E E).map_rel_iff

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6


/-- **Theorem 8.6(b)(ii) (Scott 1981, PRG-19).** `subApprox` is finitary: composing
`subApproxFixIso` with `finitaryProjectionSubsystemEquiv` and Proposition 6.11's
`subsystemReprIso` witnesses `Fix(subApprox)` as (order-isomorphic to) a genuine domain. -/
theorem isFinitary_subApprox : IsFinitary (subApprox (E := E)) :=
  ⟨_, _, ⟨subApproxFixIso.trans
    ((finitaryProjectionSubsystemEquiv E).trans (Proposition611.subsystemReprIso E))⟩⟩
end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- `fixedNbhd (sub f) = fixedNbhd f`: `Y (sub f) Y ↔ Y f Y`, since a witness `Y ⊆ Y' ⊆ Y` forces
`Y' = Y`. This is the key computation behind `sub`'s idempotency (`sub_sub`). -/
theorem fixedNbhd_sub (f : ApproximableMap E E) : fixedNbhd (sub f) = fixedNbhd f := by
  apply NeighborhoodSystem.ext
  · intro Y
    constructor
    · intro hmem
      have hr : (sub f).rel Y Y := hmem.2
      obtain ⟨hYE, -, Y', hY', hYY', hY'Y⟩ := sub_rel.mp hr
      obtain ⟨hY'E, hY'f⟩ := hY'
      have hYY'eq : Y' = Y := Set.Subset.antisymm hY'Y hYY'
      exact ⟨hYE, hYY'eq ▸ hY'f⟩
    · intro hmem
      obtain ⟨hYE, hYf⟩ := hmem
      refine ⟨hYE, sub_rel.mpr ⟨hYE, hYE, Y, ⟨hYE, hYf⟩, subset_rfl, subset_rfl⟩⟩
  · rfl
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **The easy half of Theorem 8.6's range characterization.** If `f` is a fixed point of `sub`,
then `f` is a finitary projection: `sub f = f` says exactly that `f` *is*
`retractionOfSubsystem (fixedNbhd_subsystem f)`, and Definition 8.3's corollary of Proposition 8.2
finishes immediately. (The converse — every finitary projection is a fixed point of `sub` — is
Theorem 8.5's harder direction; see the module docstring.) -/
theorem isFinitaryProjection_of_sub_eq_self {f : ApproximableMap E E} (h : sub f = f) :
    FinitaryProjection f := by
  rw [← h]
  exact Subsystem.isFinitaryProjection_retractionOfSubsystem (fixedNbhd_subsystem f)
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **`sub f ≤ f`, unconditionally (Scott 1981, PRG-19).** "`X ⊆ Y, f Y ⊆ Z` always implies
`X f Z`" — a bare narrow-input/widen-output monotonicity calculation, needing nothing about `f`. -/
theorem sub_le (f : ApproximableMap E E) : sub f ≤ f := by
  rintro X Z hr
  obtain ⟨hX, hZ, Y, ⟨hYE, hYf⟩, hXY, hYZ⟩ := sub_rel.mp hr
  have h1 : f.rel X Y := f.mono hYf hXY subset_rfl hX hYE
  exact f.mono h1 subset_rfl hYZ hX hZ
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6


/-- **`subApprox` is a projection**: `subApprox ≤ idMap`, from `subFilter φ ≤ φ`, itself
inherited from `sub_le`. -/
theorem subApprox_le_idMap : subApprox ≤ idMap (funSpace E E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_subApprox, toElementMap_idMap]
  calc subFilter φ = toFilter (sub (toApproxMap φ)) := rfl
    _ ≤ toFilter (toApproxMap φ) := toFilter_le_iff.mpr (sub_le _)
    _ = φ := toFilter_toApproxMap φ

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **The hard half of Theorem 8.6's range characterization, now unblocked by Theorem 8.5.** Every
finitary projection is a fixed point of `sub`: `⊇` is `sub_le`; `⊆` unwinds `X f Z` via
`rel_iff_mem_principal` into `Z ∈ f(↑X)`, and Theorem 8.5's formula
(`formula_of_isFinitaryProjection`) rewrites this as exactly `sub_rel`'s defining formula. -/
theorem sub_eq_self_of_isFinitaryProjection {f : ApproximableMap E E}
    (h : FinitaryProjection f) : sub f = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · exact sub_le f X Z
  · intro hXZ
    have hX : E.mem X := f.rel_dom hXZ
    have hZ : E.mem Z := f.rel_cod hXZ
    have hmem : (f.toElementMap (E.principal hX)).mem Z := (f.rel_iff_mem_principal hX).mp hXZ
    obtain ⟨-, W, hW, hWZ, hWf⟩ := (formula_of_isFinitaryProjection h (E.principal hX)).mp hmem
    obtain ⟨hWE, hXW⟩ := (E.mem_principal hX).mp hW
    exact sub_rel.mpr ⟨hX, hZ, W, ⟨hWE, hWf⟩, hXW, hWZ⟩
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Theorem 8.6's range characterization, in full.** `sub f = f ↔ f` is a finitary projection. -/
theorem sub_eq_self_iff_isFinitaryProjection {f : ApproximableMap E E} :
    sub f = f ↔ FinitaryProjection f :=
  ⟨isFinitaryProjection_of_sub_eq_self, sub_eq_self_of_isFinitaryProjection⟩
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **`sub` is idempotent: `sub (sub f) = sub f`** (sharper than Scott's stated `sub(f) ⊆
sub(sub(f))`, Theorem 8.6's projection clause for `sub` itself). Both sides are
`retractionOfSubsystem` of the *same* subsystem `fixedNbhd f` (`fixedNbhd_sub`), so they coincide
as maps, not merely as an inclusion. -/
theorem sub_sub (f : ApproximableMap E E) : sub (sub f) = sub f := by
  unfold sub
  congr 1
  exact fixedNbhd_sub f
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

/-- **`sub` is itself a finitary projection on `E → E`'s range** (Theorem 8.6's remark that `sub`
restricted to its own range is the identity, i.e. `sub` "is" a projection onto the finitary
projections): applying `sub` twice is the same as once (`sub_sub`), and every `sub f` is already a
fixed point of `sub` (feed `isFinitaryProjection_of_sub_eq_self (sub_sub f)` back through
`sub_eq_self_iff_isFinitaryProjection`) — i.e. `sub f` is *always* a finitary projection, for any
`f`, needing no hypothesis on `f` at all. -/
theorem isFinitaryProjection_sub (f : ApproximableMap E E) : FinitaryProjection (sub f) :=
  isFinitaryProjection_of_sub_eq_self (sub_sub f)
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6


theorem subFilter_subFilter (φ : (funSpace E E).Element) :
    subFilter (subFilter φ) = subFilter φ := by
  unfold subFilter
  rw [toApproxMap_toFilter, sub_sub]

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6


theorem toElementMap_subApprox_comp (φ : (funSpace E E).Element) :
    (subApprox.comp subApprox).toElementMap φ = subApprox.toElementMap φ := by
  rw [toElementMap_comp]
  simp only [toElementMap_subApprox]
  exact subFilter_subFilter φ

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6


/-- **`subApprox` is a retraction**: `subApprox ∘ subApprox = subApprox`, from `subFilter`'s own
idempotency (`subFilter_subFilter`), itself inherited from `sub_sub`. Proved via `le_antisymm` on
`le_iff_toElementMap_le` (choice-free), rather than the classical `ext_of_toElementMap`. -/
theorem isRetraction_subApprox : Retraction (subApprox (E := E)) :=
  ⟨le_antisymm (le_iff_toElementMap_le.mpr fun φ => (toElementMap_subApprox_comp φ).le)
    (le_iff_toElementMap_le.mpr fun φ => (toElementMap_subApprox_comp φ).ge)⟩

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6


/-- **`sub` is itself a *projection* on the function space `(E → E)`** (half of Theorem 8.6's
second clause; the other half, `IsFinitary subApprox`, is below). -/
theorem isProjection_subApprox : IsProjection (subApprox (E := E)) :=
  ⟨isRetraction_subApprox, subApprox_le_idMap⟩

end Sub8_6
end

section
open NeighborhoodSystem ApproximableMap
universe u
variable {α : Type u} {E : NeighborhoodSystem α}

namespace Sub8_6


/-- **Theorem 8.6(b), in full.** `subApprox` is a finitary projection on `(E → E)`. -/
theorem isFinitaryProjection_subApprox : FinitaryProjection (subApprox (E := E)) :=
  ⟨⟨isProjection_subApprox, isFinitary_subApprox⟩⟩

end Sub8_6
end

section
set_option linter.unusedVariables false

theorem theorem_86.{u} : And
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      Iff
        (@Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.sub α E f)
          f)
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E f))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.IsFinitary (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
        (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E)))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E)) :=
  @And.intro
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      Iff
        (@Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.sub α E f)
          f)
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E f))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.IsFinitary (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
        (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E)))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E))
  (@And.intro
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      Iff
        (@Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.sub α E f)
          f)
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E f))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.IsFinitary (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E))
    @DomainTheory.NeighbourhoodSystems.sub_eq_self_iff_isFinitaryProjection
    @DomainTheory.NeighbourhoodSystems.Sub8_6.isFinitary_subApprox)
  @DomainTheory.NeighbourhoodSystems.Sub8_6.isFinitaryProjection_subApprox
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6
variable {α : Type*} {E : NeighborhoodSystem α}

/-- **`subApprox`'s relation, unfolded via `ofMono`/`ofContinuous`/`toFilter`.** `F subApprox G`
holds iff `G` is a genuine function-space neighbourhood containing `sub` of `F`'s least map (any
witnessing proof `hF` of `F`'s membership works, by proof irrelevance). -/
theorem subApprox_rel_iff {F G : Set (ApproximableMap E E)} (hF : (funSpace E E).mem F) :
    (subApprox (E := E)).rel F G ↔
      (funSpace E E).mem G ∧ sub (toApproxMap ((funSpace E E).principal hF)) ∈ G :=
  ⟨fun ⟨_, hG, hmem⟩ => ⟨hG, hmem⟩, fun ⟨hG, hmem⟩ => ⟨hF, hG, hmem⟩⟩
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6
variable {α : Type*} {E : NeighborhoodSystem α}

section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)

/-- **`subApprox`'s relation, specialized to `Xenum`.** `(Xenum n) subApprox (Xenum m)` holds iff,
whenever `m` is consistent, `sub` of `Xenum n`'s least map relates every coded step of `Xenum m`. -/
theorem subApprox_rel_Xenum_iff (n m : ℕ) :
    (subApprox (E := E)).rel (Xenum P P gN n) (Xenum P P gN m) ↔
      gN m = 1 → ∀ e ∈ decodeList m,
        (sub (toApproxMap ((funSpace E E).principal (Xenum_mem P P gN hgN n)))).rel
          (P.X e.unpair.1) (P.X e.unpair.2) := by
  rw [subApprox_rel_iff (Xenum_mem P P gN hgN n), and_iff_right (Xenum_mem P P gN hgN m)]
  exact mem_Xenum_iff_map P P gN _ m

end SubComputable
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6
variable {α : Type*} {E : NeighborhoodSystem α}

section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)


/-- **The per-witness `sub`-step predicate is recursively decidable**, coded as a function of
`w = ⟨y, ⟨n, e⟩⟩`: the function-space inclusion `Xenum n ⊆ Xenum (codePair y y)` (via `fincl`, the
function-space presentation's own inclusion char) conjoined with the two `𝒟`-inclusions bracketing
`y` (via `incl`, `P`'s own inclusion char). -/
theorem subStep_recDecidable (fincl incl : ℕ → ℕ)
    (hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2)
    (hfinclp : Nat.Primrec fincl)
    (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl) :
    RecDecidable (fun w : ℕ =>
      Xenum P P gN w.unpair.2.unpair.1 ⊆ Xenum P P gN (codePair w.unpair.1 w.unpair.1) ∧
        P.X w.unpair.2.unpair.2.unpair.1 ⊆ P.X w.unpair.1 ∧
          P.X w.unpair.1 ⊆ P.X w.unpair.2.unpair.2.unpair.2) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he1 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hcodeYY : Nat.Primrec (fun w : ℕ => codePair w.unpair.1 w.unpair.1) :=
    Nat.Primrec.succ.comp ((hy.pair hy).pair (Nat.Primrec.const 0))
  have h1 : RecDecidable (fun w : ℕ =>
      Xenum P P gN w.unpair.2.unpair.1 ⊆ Xenum P P gN (codePair w.unpair.1 w.unpair.1)) :=
    ⟨fun w => fincl (Nat.pair w.unpair.2.unpair.1 (codePair w.unpair.1 w.unpair.1)),
      hfinclp.comp (hn.pair hcodeYY), fun w => by
        rw [hfincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  have h2 : RecDecidable (fun w : ℕ => P.X w.unpair.2.unpair.2.unpair.1 ⊆ P.X w.unpair.1) :=
    ⟨fun w => incl (Nat.pair w.unpair.2.unpair.2.unpair.1 w.unpair.1), hinclp.comp (he1.pair hy),
      fun w => by rw [hincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  have h3 : RecDecidable (fun w : ℕ => P.X w.unpair.1 ⊆ P.X w.unpair.2.unpair.2.unpair.2) :=
    ⟨fun w => incl (Nat.pair w.unpair.1 w.unpair.2.unpair.2.unpair.2), hinclp.comp (hy.pair he2),
      fun w => by rw [hincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  exact h1.and (h2.and h3)

end SubComputable
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6
variable {α : Type*} {E : NeighborhoodSystem α}

section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)

/-- **`sub`'s defining existential, reindexed to presentation indices.** `sub f` relates presented
neighbourhoods `X_a`, `X_b` iff some presented `X_y` witnesses Scott's formula (`P.surj` turns the
arbitrary witness neighbourhood `Y` of `sub_rel` into an index `y`). -/
theorem sub_rel_iff_exists_index {f : ApproximableMap E E} {a b : ℕ} :
    (sub f).rel (P.X a) (P.X b) ↔
      ∃ y : ℕ, f.rel (P.X y) (P.X y) ∧ P.X a ⊆ P.X y ∧ P.X y ⊆ P.X b := by
  rw [sub_rel, and_iff_right (P.mem_X a), and_iff_right (P.mem_X b)]
  constructor
  · rintro ⟨Y, ⟨hYE, hYf⟩, haY, hYb⟩
    obtain ⟨y, rfl⟩ := P.surj hYE
    exact ⟨y, hYf, haY, hYb⟩
  · rintro ⟨y, hYf, haY, hYb⟩
    exact ⟨P.X y, ⟨P.mem_X y, hYf⟩, haY, hYb⟩

end SubComputable
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6
variable {α : Type*} {E : NeighborhoodSystem α}

section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)

/-- **`sub` of `Xenum n`'s least map, in fully decidable-existential form.** Combines
`sub_rel_iff_exists_index` with Theorem 7.6's `leastMap_Xenum_rel`/`Xenum_codePair` to turn the
witness condition `ĝₙ.rel (X_y) (X_y)` into the recursively decidable function-space inclusion
`Xenum n ⊆ Xenum (codePair y y)`. -/
theorem sub_leastMap_rel_iff (n a b : ℕ) :
    (sub (toApproxMap ((funSpace E E).principal (Xenum_mem P P gN hgN n)))).rel
        (P.X a) (P.X b) ↔
      ∃ y : ℕ, Xenum P P gN n ⊆ Xenum P P gN (codePair y y) ∧
        P.X a ⊆ P.X y ∧ P.X y ⊆ P.X b := by
  rw [sub_rel_iff_exists_index P]
  refine exists_congr (fun y => ?_)
  rw [leastMap_Xenum_rel P gN hgN n y y, Xenum_codePair P gN hgN y y]

end SubComputable
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6
variable {α : Type*} {E : NeighborhoodSystem α}

section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)


/-- **Theorem 8.6(c) (Scott 1981, PRG-19), as an `ComputableMap` statement.** Relative to the
function-space presentation `funPresentation P P …` (Theorem 7.5) built from any presentation `P` of
`E`, `subApprox` is computable: its neighbourhood relation is the recursively enumerable
`¬(consistent m) ∨ ∀ e ∈ decodeList m, ∃ y, …` (a bounded `∀` of an unbounded `∃` of a decidable
predicate). -/
theorem subApprox_isComputable
    (incl eq : ℕ → ℕ)
    (hgNp : Nat.Primrec gN)
    (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl)
    (heq : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2) (heqp : Nat.Primrec eq) :
    ComputableMap
      (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp)
      (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp)
      (subApprox (E := E)) := by
  constructor
  obtain ⟨fincl, hfinclp, hfincls⟩ :=
    (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp).incl_computable
  have hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2 :=
    fun s => (hfincls s).symm
  show REPred₂ (fun n m => (subApprox (E := E)).rel (Xenum P P gN n) (Xenum P P gN m))
  have hdec := subStep_recDecidable P gN fincl incl hfincl hfinclp hincl hinclp
  have hre : REPred₂ (fun n e => ∃ y : ℕ,
      Xenum P P gN n ⊆ Xenum P P gN (codePair y y) ∧
        P.X e.unpair.1 ⊆ P.X y ∧ P.X y ⊆ P.X e.unpair.2) := by
    refine REPred.of_iff (fun t => ?_) hdec.re.proj
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hforall : REPred (fun t => ∀ e ∈ decodeList t.unpair.2, ∃ y : ℕ,
      Xenum P P gN t.unpair.1 ⊆ Xenum P P gN (codePair y y) ∧
        P.X e.unpair.1 ⊆ P.X y ∧ P.X y ⊆ P.X e.unpair.2) :=
    REPred.forall_mem_decodeList₂ hre
  have hne1 : REPred (fun t => ¬ gN t.unpair.2 = 1) :=
    ((RecDecidable.natEq (hgNp.comp Nat.Primrec.right) (Nat.Primrec.const 1)).not).re
  refine REPred.of_iff (fun t => ?_) (hne1.or hforall)
  show (subApprox (E := E)).rel (Xenum P P gN t.unpair.1) (Xenum P P gN t.unpair.2) ↔ _
  rw [subApprox_rel_Xenum_iff P gN hgN t.unpair.1 t.unpair.2, Decidable.imp_iff_not_or]
  refine or_congr_right (forall_congr' (fun e => imp_congr_right (fun _ => ?_)))
  exact sub_leastMap_rel_iff P gN hgN t.unpair.1 e.unpair.1 e.unpair.2

end SubComputable
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6
variable {α : Type*} {E : NeighborhoodSystem α}

/-- **Theorem 8.6(c) (Scott 1981, PRG-19), in full: "If `E` is effectively given, then `sub` is
computable."** Packages `subApprox_isComputable` with the function-space presentation that Theorem
7.5 (`funSpace_isEffectivelyGiven`'s construction, `funPresentation`) builds out of any computable
presentation of `E`. -/
theorem sub_isComputable_of_isEffectivelyGiven (h : E.IsEffectivelyGiven) :
    ∃ Pfun : ComputablePresentation (funSpace E E),
      ComputableMap Pfun Pfun (subApprox (E := E)) := by
  obtain ⟨P⟩ := h
  obtain ⟨incl, hinclp, hincls⟩ := P.incl_computable
  obtain ⟨eq, heqp, heqs⟩ := P.eq_computable
  obtain ⟨fc, hfcp, hfcs⟩ := P.cons_computable
  have hincl' : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2 := fun s => (hincls s).symm
  have heq' : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2 := fun s => (heqs s).symm
  have hgN : ∀ c, funConsChar P P fc fc c = 1 ↔
      (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty :=
    fun c => funConsChar_spec P P fc fc (fun s => (hfcs s).symm) (fun s => (hfcs s).symm) c
  refine ⟨funPresentation P P (funConsChar P P fc fc) incl incl eq hgN
    (primrec_funConsChar P P fc fc hfcp hfcp) hincl' hinclp hincl' hinclp heq' heqp,
    subApprox_isComputable P (funConsChar P P fc fc) hgN incl eq
      (primrec_funConsChar P P fc fc hfcp hfcp) hincl' hinclp heq' heqp⟩
end

section
set_option linter.unusedVariables false

theorem theorem_86_c.{u_1} : And
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α E) (gN : Nat → Nat)
    (hgN :
      ∀ (c : Nat),
        Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.stepFun α α E E
              (@DomainTheory.NeighbourhoodSystems.funListOf α α E E P P (Domain.Recursive.decodeList c)))))
    (incl eq : Nat → Nat) (hgNp : Nat.Primrec gN)
    (hincl :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set α) (@Set.instLE α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hinclp : Nat.Primrec incl)
    (heq :
      ∀ (s : Nat),
        Iff (@Eq Nat (eq s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq (Set α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (heqp : Nat.Primrec eq),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E))
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α E →
      ∃ (Pfun :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
        @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
          Pfun Pfun (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E)) :=
  @And.intro
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α E) (gN : Nat → Nat)
    (hgN :
      ∀ (c : Nat),
        Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@DomainTheory.NeighbourhoodSystems.stepFun α α E E
              (@DomainTheory.NeighbourhoodSystems.funListOf α α E E P P (Domain.Recursive.decodeList c)))))
    (incl eq : Nat → Nat) (hgNp : Nat.Primrec gN)
    (hincl :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set α) (@Set.instLE α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hinclp : Nat.Primrec incl)
    (heq :
      ∀ (s : Nat),
        Iff (@Eq Nat (eq s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq (Set α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α E P (@Prod.snd Nat Nat (Nat.unpair s)))))
    (heqp : Nat.Primrec eq),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.funPresentation α α E E P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp
        heq heqp)
      (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E))
  (∀ {α : Type u_1} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α E →
      ∃ (Pfun :
        @DomainTheory.NeighbourhoodSystems.ComputablePresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)),
        @DomainTheory.NeighbourhoodSystems.ComputableMap (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
          (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
          Pfun Pfun (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E))
  @DomainTheory.NeighbourhoodSystems.subApprox_isComputable
  @DomainTheory.NeighbourhoodSystems.sub_isComputable_of_isEffectivelyGiven
end

section
open NeighborhoodSystem
variable {α : Type*}

/-- **The abstract specification a splitting operation must satisfy** — exactly `exists_split`'s
conclusion, as a `Prop` about a *total* function `split`. Both the classical `splitChoice` (via
`Classical.choice`) and the effective, computable `splitEff` (Theorem 8.8(b)) satisfy this. -/
def SplitSpec (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ) : Prop :=
  ∀ {A : Set α} {B : Set ℚ}, (A = ∅ ↔ B = ∅) → (B = ∅ ∨ U.mem B) → ∀ Xn : Set α,
    ((split A B Xn).1 = ∅ ∨ U.mem (split A B Xn).1) ∧
      ((split A B Xn).2 = ∅ ∨ U.mem (split A B Xn).2) ∧
      (A ∩ Xn = ∅ ↔ (split A B Xn).1 = ∅) ∧
      (A \ Xn = ∅ ↔ (split A B Xn).2 = ∅) ∧
      (split A B Xn).1 ∪ (split A B Xn).2 = B ∧
      (split A B Xn).1 ∩ (split A B Xn).2 = ∅
end

section
open NeighborhoodSystem
variable {α : Type*}

/-- **The key local splitting step behind Theorem 8.8(a)'s back-and-forth construction.** Given a
`D`-side atom `A` matched with a `U`-side atom `B` (`A = ∅ ↔ B = ∅`, and `B` is either empty or a
genuine `U`-neighbourhood), and a new target set `Xₙ` (morally the next `D`-neighbourhood `Xₙ`),
produce matching refinements `I` (for `A ∩ Xₙ`) and `J` (for `A \ Xₙ`). -/
theorem exists_split {A : Set α} {B : Set ℚ} (hAB : A = ∅ ↔ B = ∅)
    (hBU : B = ∅ ∨ U.mem B) (Xn : Set α) :
    ∃ I J : Set ℚ, (I = ∅ ∨ U.mem I) ∧ (J = ∅ ∨ U.mem J) ∧
      (A ∩ Xn = ∅ ↔ I = ∅) ∧ (A \ Xn = ∅ ↔ J = ∅) ∧ I ∪ J = B ∧ I ∩ J = ∅ := by
  by_cases h1 : A ∩ Xn = ∅
  · refine ⟨∅, B, Or.inl rfl, hBU, by simp [h1], ?_, by simp, by simp⟩
    have hAeq : A \ Xn = A := by
      ext x
      simp only [Set.mem_sdiff]
      refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun hxn => ?_⟩⟩
      exact Set.eq_empty_iff_forall_notMem.mp h1 x ⟨hx, hxn⟩
    rw [hAeq, hAB]
  · by_cases h2 : A \ Xn = ∅
    · refine ⟨B, ∅, hBU, Or.inl rfl, ?_, iff_of_true h2 rfl, by simp, by simp⟩
      have hAeq : A ∩ Xn = A := by
        ext x
        simp only [Set.mem_inter_iff]
        refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
        by_contra hxn
        exact Set.eq_empty_iff_forall_notMem.mp h2 x ⟨hx, hxn⟩
      rw [hAeq, hAB]
    · have hAne : A ≠ ∅ := by
        intro hA
        apply h1
        rw [hA]
        exact Set.empty_inter Xn
      have hBne : B ≠ ∅ := fun hB => hAne (hAB.mpr hB)
      have hBU' : U.mem B := hBU.resolve_left hBne
      obtain ⟨Y, Z, hY, hZ, hYZinter, hYZunion, -, -⟩ := U_no_minimal hBU'
      have hYne : Y ≠ ∅ := hY.2.1.ne_empty
      have hZne : Z ≠ ∅ := hZ.2.1.ne_empty
      exact ⟨Y, Z, Or.inr hY, Or.inr hZ, iff_of_false h1 hYne, iff_of_false h2 hZne,
        hYZunion, hYZinter⟩
end

section
open NeighborhoodSystem
variable {α : Type*}

def genAtom {β : Type*} (Z : ℕ → Set β) (M : Set β) (δ : ℕ → Bool) : ℕ → Set β
  | 0 => M
  | (n + 1) => genAtom Z M δ n ∩ (if δ n then Z n else M \ Z n)
end

section
open NeighborhoodSystem
variable {α : Type*}
variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)

/-- The `U`-side atom matching `genAtom X Δ δ n`, built recursively via an abstract splitting
operation `split` (instantiated with `splitChoice` for Theorem 8.8(a), `splitEff` for 8.8(b)). -/
noncomputable def atomU (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
    (X : ℕ → Set α) (Δ : Set α) (δ : ℕ → Bool) : ℕ → Set ℚ
  | 0 => U.master
  | (n + 1) =>
      if δ n then (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).2
end

section
open NeighborhoodSystem
variable {α : Type*}
variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
variable (X : ℕ → Set α) (Δ : Set α)

@[simp] theorem atomU_zero (δ : ℕ → Bool) : atomU split X Δ δ 0 = U.master := rfl
end

section
open NeighborhoodSystem
variable {α : Type*}
variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
variable (X : ℕ → Set α) (Δ : Set α)
variable (hΔ : Δ.Nonempty) (hsplit : SplitSpec split)
include hΔ hsplit

/-- Pad `δ' : Fin n → Bool` to a total `ℕ → Bool`, filling positions `≥ n` with `true`. -/
def extendTrue {n : ℕ} (δ' : Fin n → Bool) : ℕ → Bool :=
  fun i => if h : i < n then δ' ⟨i, h⟩ else true
end

section
open NeighborhoodSystem
variable {α : Type*}
variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
variable (X : ℕ → Set α) (Δ : Set α)
variable (hΔ : Δ.Nonempty) (hsplit : SplitSpec split)
include hΔ hsplit

/-- **Scott's `Yₙ`**: the union, over all `2ⁿ` depth-`n` atoms, of the "+"-piece chosen when
splitting against `X n`. -/
noncomputable def Yseq (n : ℕ) : Set ℚ :=
  ⋃ δ' : Fin n → Bool, atomU split X Δ (extendTrue δ') (n + 1)
end

section
open NeighborhoodSystem
variable {α : Type*}
variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
variable (X : ℕ → Set α) (Δ : Set α)
variable (hΔ : Δ.Nonempty) (hsplit : SplitSpec split)
include hΔ hsplit

/-- Restrict `δ : ℕ → Bool` to `Fin n → Bool`. -/
def restrictFin (δ : ℕ → Bool) (n : ℕ) : Fin n → Bool := fun i => δ i.val
end

section
open NeighborhoodSystem
variable {α : Type*}

open Classical in
/-- **Total packaging of `exists_split`.** Given any `A : Set α`, `B : Set ℚ`, `Xn : Set α`,
`splitChoice A B Xn` is the pair `(I, J)` produced by `exists_split` whenever the hypotheses hold
(`A = ∅ ↔ B = ∅` and `B = ∅ ∨ U.mem B`), and the junk value `(∅, ∅)` otherwise. Making this total
(rather than threading proof obligations through a dependent recursive definition) is what lets
`atomU` below be defined by plain structural recursion on `ℕ`; `splitChoice_isSplitSpec` recovers
`exists_split`'s conclusions whenever the hypotheses genuinely hold, which is all that is ever
used (the junk branch is never reached along the real construction). -/
noncomputable def splitChoice (A : Set α) (B : Set ℚ) (Xn : Set α) : Set ℚ × Set ℚ :=
  if h : (A = ∅ ↔ B = ∅) ∧ (B = ∅ ∨ U.mem B) then
    ⟨(exists_split h.1 h.2 Xn).choose, (exists_split h.1 h.2 Xn).choose_spec.choose⟩
  else (∅, ∅)
end

section
open NeighborhoodSystem
variable {α : Type*}

theorem genAtom_subset {β : Type*} (Z : ℕ → Set β) (M : Set β) (δ : ℕ → Bool) (n : ℕ) :
    genAtom Z M δ n ⊆ M := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (Set.inter_subset_left).trans ih

/-- Extending/changing `δ` at or beyond position `n` does not change `genAtom Z M δ n`. -/
theorem genAtom_congr {β : Type*} (Z : ℕ → Set β) (M : Set β) {δ δ' : ℕ → Bool} {n : ℕ}
    (h : ∀ i < n, δ i = δ' i) : genAtom Z M δ n = genAtom Z M δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    have hprev : genAtom Z M δ n = genAtom Z M δ' n := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    show genAtom Z M δ n ∩ _ = genAtom Z M δ' n ∩ _
    rw [hprev, hn]

/-- **Forward direction of atom membership**: if `x` lies in the depth-`n` atom for `δ`, then `δ`
records `x`'s membership pattern against `Z 0, …, Z (n-1)` exactly. (The converse, "self-atom
membership" for the canonical `δ` built from `x` itself, is `genAtom_self` below; together they
are all that is needed — no general "iff" characterization with explicit list/`Fin` indexing is
required anywhere in this file.) -/
theorem genAtom_forward {β : Type*} {Z : ℕ → Set β} {M : Set β} {δ : ℕ → Bool} {n : ℕ}
    {x : β} (hx : x ∈ genAtom Z M δ n) : ∀ i < n, (δ i = true ↔ x ∈ Z i) := by
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi
    obtain ⟨hxprev, hxlast⟩ := hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact ih hxprev i hi'
    · by_cases hδ : δ i = true
      · simp only [hδ, ite_true] at hxlast
        exact ⟨fun _ => hxlast, fun _ => hδ⟩
      · rw [Bool.not_eq_true] at hδ
        simp only [hδ] at hxlast
        exact ⟨fun h => absurd h (by simp [hδ]), fun hmem => absurd hmem hxlast.2⟩

open Classical in
/-- **Self-atom membership**: any `x ∈ M` lies in its own canonical atom (built from the
sign sequence `δ := fun k => decide (x ∈ Z k)`), at every depth `n`. -/
theorem genAtom_self {β : Type*} (Z : ℕ → Set β) (M : Set β) {x : β} (hx : x ∈ M) :
    ∀ n, x ∈ genAtom Z M (fun k => decide (x ∈ Z k)) n := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih =>
    refine ⟨ih, ?_⟩
    by_cases h : x ∈ Z n
    · simp [h]
    · simp [h, hx]


/-- **A splitting operation's first output is a subset of `B`** (`I ⊆ B`, from `I ∪ J = B`) —
a corollary of `SplitSpec` alone, needing no facts about the specific `split`. -/
theorem split_fst_subset {split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ} (hsplit : SplitSpec split)
    {A : Set α} {B : Set ℚ} (hAB : A = ∅ ↔ B = ∅)
    (hBU : B = ∅ ∨ U.mem B) (Xn : Set α) : (split A B Xn).1 ⊆ B :=
  Set.subset_union_left.trans_eq (hsplit hAB hBU Xn).2.2.2.2.1

/-- **A splitting operation's second output is a subset of `B`** (`J ⊆ B`, from `I ∪ J = B`). -/
theorem split_snd_subset {split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ} (hsplit : SplitSpec split)
    {A : Set α} {B : Set ℚ} (hAB : A = ∅ ↔ B = ∅)
    (hBU : B = ∅ ∨ U.mem B) (Xn : Set α) : (split A B Xn).2 ⊆ B :=
  Set.subset_union_right.trans_eq (hsplit hAB hBU Xn).2.2.2.2.1

variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)


variable (X : ℕ → Set α) (Δ : Set α)


theorem atomU_succ (δ : ℕ → Bool) (n : ℕ) :
    atomU split X Δ δ (n + 1) =
      if δ n then (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).2 := rfl

/-- Extending/changing `δ` at or beyond position `n` does not change `atomU split X Δ δ n` (mirrors
`genAtom_congr`; needs no invariant, since `split` is an ordinary function of its inputs). -/
theorem atomU_congr {δ δ' : ℕ → Bool} {n : ℕ} (h : ∀ i < n, δ i = δ' i) :
    atomU split X Δ δ n = atomU split X Δ δ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hprev : atomU split X Δ δ n = atomU split X Δ δ' n :=
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hA : genAtom X Δ δ n = genAtom X Δ δ' n :=
      genAtom_congr X Δ (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hn := h n (Nat.lt_succ_self n)
    rw [atomU_succ, atomU_succ, hA, hprev, hn]

variable (hΔ : Δ.Nonempty) (hsplit : SplitSpec split)
include hΔ hsplit

/-- **The core invariant of Scott's back-and-forth construction**, proved by a single induction on
`n` alongside `split`'s spec: at every depth `n` and for every sign sequence `δ`,
(a) the atom-matching invariant `(■)` (`genAtom X Δ δ n = ∅ ↔ atomU split X Δ δ n = ∅`),
(b) `atomU split X Δ δ n` is either empty or a genuine `U`-neighbourhood, and
(c) **pairwise disjointness**: atoms for sign sequences disagreeing somewhere below `n` are
disjoint on the `U`-side. (c) is what lets `Yseq` (below) recover a *closed-form* recursive
description of `atomU`, exactly mirroring `genAtom`'s. -/
theorem atomU_invariant :
    ∀ n, (∀ δ, genAtom X Δ δ n = ∅ ↔ atomU split X Δ δ n = ∅) ∧
      (∀ δ, atomU split X Δ δ n = ∅ ∨ U.mem (atomU split X Δ δ n)) ∧
      (∀ δ δ', (∃ i < n, δ i ≠ δ' i) →
        atomU split X Δ δ n ∩ atomU split X Δ δ' n = ∅) := by
  have hUmasterNe : (U.master : Set ℚ) ≠ ∅ := Set.Nonempty.ne_empty ⟨0, by norm_num [U]⟩
  intro n
  induction n with
  | zero =>
    refine ⟨fun δ => ?_, fun δ => Or.inr U.master_mem, fun δ δ' ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
    show Δ = ∅ ↔ (U.master : Set ℚ) = ∅
    exact ⟨fun h => absurd h hΔ.ne_empty, fun h => absurd h hUmasterNe⟩
  | succ n ih =>
    obtain ⟨ihmatch, ihmem, ihdisj⟩ := ih
    refine ⟨fun δ => ?_, fun δ => ?_, fun δ δ' ⟨i, hi, hne⟩ => ?_⟩
    · have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
      rw [atomU_succ]
      by_cases hδ : δ n = true
      · rw [show genAtom X Δ δ (n + 1) = genAtom X Δ δ n ∩ X n from by simp [genAtom, hδ]]
        simp only [hδ, ite_true]
        exact hspec.2.2.1
      · rw [Bool.not_eq_true] at hδ
        have hsub := genAtom_subset X Δ δ n
        rw [show genAtom X Δ δ (n + 1) = genAtom X Δ δ n \ X n from by
          have heq : genAtom X Δ δ (n + 1) = genAtom X Δ δ n ∩ (Δ \ X n) := by simp [genAtom, hδ]
          rw [heq]
          ext x; constructor
          · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩
          · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩]
        simp only [hδ]
        exact hspec.2.2.2.1
    · have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
      rw [atomU_succ]
      by_cases hδ : δ n = true
      · simp only [hδ, ite_true]; exact hspec.1
      · simp only [hδ]; exact hspec.2.1
    · by_cases hagree : ∀ j < n, δ j = δ' j
      · have hδn : δ n ≠ δ' n := by
          intro heq
          exact hne (by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
            · exact hagree i hi'
            · exact heq)
        have hA : genAtom X Δ δ n = genAtom X Δ δ' n := genAtom_congr X Δ hagree
        have hB : atomU split X Δ δ n = atomU split X Δ δ' n := atomU_congr split X Δ hagree
        have hspec := hsplit (ihmatch δ) (ihmem δ) (X n)
        rw [atomU_succ, atomU_succ, hA, hB]
        have hIJ := hspec.2.2.2.2.2
        rcases Bool.eq_false_or_eq_true (δ n) with h1 | h1 <;>
          rcases Bool.eq_false_or_eq_true (δ' n) with h2 | h2 <;>
          simp_all [Set.inter_comm]
      · push Not at hagree
        obtain ⟨j, hj, hjne⟩ := hagree
        have hd : atomU split X Δ δ n ∩ atomU split X Δ δ' n = ∅ := ihdisj δ δ' ⟨j, hj, hjne⟩
        have h1 : atomU split X Δ δ (n + 1) ⊆ atomU split X Δ δ n := by
          rw [atomU_succ]
          by_cases hδ : δ n = true
          · simp only [hδ, ite_true]; exact split_fst_subset hsplit (ihmatch δ) (ihmem δ) (X n)
          · simp only [hδ]; exact split_snd_subset hsplit (ihmatch δ) (ihmem δ) (X n)
        have h2 : atomU split X Δ δ' (n + 1) ⊆ atomU split X Δ δ' n := by
          rw [atomU_succ]
          by_cases hδ' : δ' n = true
          · simp only [hδ', ite_true]; exact split_fst_subset hsplit (ihmatch δ') (ihmem δ') (X n)
          · simp only [hδ']; exact split_snd_subset hsplit (ihmatch δ') (ihmem δ') (X n)
        exact Set.subset_eq_empty (Set.inter_subset_inter h1 h2) hd

/-- Corollary of `atomU_invariant`, extracted for reuse: `atomU` only shrinks as `n` grows. -/
theorem atomU_succ_subset (δ : ℕ → Bool) (n : ℕ) :
    atomU split X Δ δ (n + 1) ⊆ atomU split X Δ δ n := by
  obtain ⟨hmatch, hmem, -⟩ := atomU_invariant split X Δ hΔ hsplit n
  rw [atomU_succ]
  by_cases hδ : δ n = true
  · simp only [hδ, ite_true]; exact split_fst_subset hsplit (hmatch δ) (hmem δ) (X n)
  · simp only [hδ]; exact split_snd_subset hsplit (hmatch δ) (hmem δ) (X n)


omit hΔ hsplit in
theorem extendTrue_agree {n : ℕ} (δ' : Fin n → Bool) (i : ℕ) (hi : i < n) :
    extendTrue δ' i = δ' ⟨i, hi⟩ := by simp [extendTrue, hi]

omit hΔ hsplit in
theorem extendTrue_restrictFin_agree (δ : ℕ → Bool) (n i : ℕ) (hi : i < n) :
    extendTrue (restrictFin δ n) i = δ i := by simp [extendTrue, restrictFin, hi]


omit hΔ hsplit in
theorem subset_Yseq {n : ℕ} (δ' : Fin n → Bool) :
    atomU split X Δ (extendTrue δ') (n + 1) ⊆ Yseq split X Δ n :=
  Set.subset_iUnion (fun δ' => atomU split X Δ (extendTrue δ') (n + 1)) δ'

/-- **The "I-formula"**: the "+"-piece chosen when splitting the depth-`n` atom for `δ` against
`X n` is *exactly* the intersection of that atom with `Yseq n` — recovering, after the fact, a
closed-form description of the choice made by `split`. This is where pairwise disjointness
(`atomU_invariant`'s third clause) is essential: it rules out any *other* depth-`n` atom (from a
different, non-agreeing `δ`) contributing a point to `Yseq n` that isn't already forced into this
one. -/
theorem split_fst_eq_inter_Yseq (δ : ℕ → Bool) (n : ℕ) :
    (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1 =
      atomU split X Δ δ n ∩ Yseq split X Δ n := by
  obtain ⟨hmatch, hmem, hdisj⟩ := atomU_invariant split X Δ hΔ hsplit n
  set A := genAtom X Δ δ n with hAdef
  set B := atomU split X Δ δ n with hBdef
  set I := (split A B (X n)).1 with hIdef
  set δ2 := Function.update δ n true with hδ2def
  set δ3 := extendTrue (restrictFin δ2 n) with hδ3def
  have hagreefull : ∀ i < n + 1, δ3 i = δ2 i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact extendTrue_restrictFin_agree δ2 n i hi'
    · simp [hδ3def, extendTrue, hδ2def]
  have hI_eq : atomU split X Δ δ2 (n + 1) = I := by
    rw [atomU_succ]
    have hd2n : δ2 n = true := by simp [hδ2def]
    have hA2 : genAtom X Δ δ2 n = A := by
      apply genAtom_congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    have hB2 : atomU split X Δ δ2 n = B := by
      apply atomU_congr; intro i hi; simp [hδ2def, Function.update_of_ne (ne_of_lt hi)]
    rw [hd2n, ite_eq_left rfl, hA2, hB2]
  have hδ3_eq : atomU split X Δ δ3 (n + 1) = I := (atomU_congr split X Δ hagreefull).trans hI_eq
  apply Set.Subset.antisymm
  · have hIsubB : I ⊆ B := split_fst_subset hsplit (hmatch δ) (hmem δ) (X n)
    have hIsubY : I ⊆ Yseq split X Δ n := hδ3_eq ▸ subset_Yseq split X Δ (restrictFin δ2 n)
    exact Set.subset_inter hIsubB hIsubY
  · rintro z ⟨hzB, hzY⟩
    obtain ⟨δ', hz'⟩ := Set.mem_iUnion.mp hzY
    by_cases hagree : ∀ i < n, extendTrue δ' i = δ i
    · have hAeq : genAtom X Δ (extendTrue δ') n = A := genAtom_congr X Δ hagree
      have hBeq : atomU split X Δ (extendTrue δ') n = B := atomU_congr split X Δ hagree
      have hlast : extendTrue δ' n = true := by simp [extendTrue]
      have heq : atomU split X Δ (extendTrue δ') (n + 1) = I := by
        rw [atomU_succ, hAeq, hBeq, hlast, ite_eq_left rfl]
      rwa [heq] at hz'
    · push Not at hagree
      obtain ⟨j, hj, hjne⟩ := hagree
      have hzB' : z ∈ atomU split X Δ (extendTrue δ') n :=
        atomU_succ_subset split X Δ hΔ hsplit (extendTrue δ') n hz'
      have hempty := hdisj δ (extendTrue δ') ⟨j, hj, fun h => hjne (h.symm)⟩
      exact absurd (Set.mem_inter hzB hzB') (by rw [hempty]; simp)

theorem atomU_subset_master (δ : ℕ → Bool) (n : ℕ) : atomU split X Δ δ n ⊆ U.master := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (atomU_succ_subset split X Δ hΔ hsplit δ n).trans ih

/-- **Closed form for `atomU`**: with `Yseq` in hand, `atomU` satisfies exactly the same
recursive description as `genAtom Yseq U.master` — the choices made by `split` are, after
the fact, forced (`split_fst_eq_inter_Yseq` handles the `true` branch; the `false` branch
follows algebraically from `I ∪ J = B`, `I ∩ J = ∅`). -/
theorem atomU_succ_eq (δ : ℕ → Bool) (n : ℕ) :
    atomU split X Δ δ (n + 1) =
      atomU split X Δ δ n ∩ (if δ n then Yseq split X Δ n else U.master \ Yseq split X Δ n) := by
  obtain ⟨hmatch, hmem, -⟩ := atomU_invariant split X Δ hΔ hsplit n
  have hspec := hsplit (hmatch δ) (hmem δ) (X n)
  have hIeq := split_fst_eq_inter_Yseq split X Δ hΔ hsplit δ n
  by_cases hδ : δ n = true
  · rw [atomU_succ, ite_eq_left hδ, ite_eq_left hδ]; exact hIeq
  · rw [atomU_succ, ite_eq_right hδ, ite_eq_right hδ]
    have hJeq : (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).2 =
        atomU split X Δ δ n \ Yseq split X Δ n := by
      have hunion := hspec.2.2.2.2.1
      have hinter := hspec.2.2.2.2.2
      ext x
      constructor
      · intro hxJ
        have hxB : x ∈ atomU split X Δ δ n := hunion ▸ Or.inr hxJ
        refine ⟨hxB, fun hxY => ?_⟩
        have hxI : x ∈ (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1 :=
          hIeq ▸ Set.mem_inter hxB hxY
        exact absurd (Set.mem_inter hxI hxJ) (by rw [hinter]; simp)
      · rintro ⟨hxB, hxnY⟩
        rw [← hunion] at hxB
        rcases hxB with hxI | hxJ
        · exact absurd (hIeq ▸ hxI : x ∈ atomU split X Δ δ n ∩ Yseq split X Δ n).2 hxnY
        · exact hxJ
    rw [hJeq]
    have hsub := atomU_subset_master split X Δ hΔ hsplit δ n
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, hsub hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩

/-- **`atomU` coincides with the generic atom construction on `Yseq`/`U.master`.** This is the
payoff of the whole `split`/disjointness apparatus: it lets every later argument treat
`atomU` and `genAtom` uniformly (in particular, `genAtom_forward` and `genAtom_self` — proved once,
generically — now apply verbatim to the `U`-side atoms too). -/
theorem atomU_eq_genAtom (δ : ℕ → Bool) :
    ∀ n, atomU split X Δ δ n = genAtom (Yseq split X Δ) U.master δ n
  | 0 => rfl
  | (n + 1) => by
      rw [atomU_succ_eq split X Δ hΔ hsplit, atomU_eq_genAtom δ n]; rfl

-- One-directional half of the transfer lemma, stated fully generically (over two independent
-- carrier types related only by a shared `genAtom`-emptiness correspondence `hcore`) so that it
-- can be reused, symmetrically, for both directions of the two-sided statement
-- `transfer_empty_iff`. Not `private`: also reused verbatim by `Exercise812cYseq.lean`'s
-- `transfer_empty_iffE` (8.12(c)(vi)(2)), since it is already fully generic over two independent
-- carrier types.
omit hΔ hsplit in
theorem transfer_dir {β1 β2 : Type*} (Z1 : ℕ → Set β1) (M1 : Set β1) (Z2 : ℕ → Set β2)
    (M2 : Set β2) (hcore : ∀ δ n, genAtom Z1 M1 δ n = ∅ ↔ genAtom Z2 M2 δ n = ∅)
    {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n)
    (hne : {x ∈ M1 | ∀ p ∈ cs, (p.2 = true ↔ x ∈ Z1 p.1)}.Nonempty) :
    {y ∈ M2 | ∀ p ∈ cs, (p.2 = true ↔ y ∈ Z2 p.1)}.Nonempty := by
  classical
  obtain ⟨x, hxM, hxcs⟩ := hne
  set δ0 : ℕ → Bool := fun k => decide (x ∈ Z1 k) with hδ0def
  have hX1 : x ∈ genAtom Z1 M1 δ0 n := genAtom_self Z1 M1 hxM n
  have hne1 : (genAtom Z1 M1 δ0 n).Nonempty := ⟨x, hX1⟩
  have hne2 : (genAtom Z2 M2 δ0 n).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h2 => hne1.ne_empty ((hcore δ0 n).mpr h2)
  obtain ⟨y, hy⟩ := hne2
  refine ⟨y, genAtom_subset Z2 M2 δ0 n hy, fun p hp => ?_⟩
  have hforward := genAtom_forward hy p.1 (hn p hp)
  have hbeq : δ0 p.1 = p.2 := by
    show decide (x ∈ Z1 p.1) = p.2
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact (hxcs p hp).symm
  rwa [hbeq] at hforward

/-- **The transfer lemma.** A finite Boolean combination of the `X i` (`i` ranging over the
finite constraint list `cs`, `true` meaning "in", `false` meaning "out") is non-empty in `D`'s
carrier `Δ` iff the *same* Boolean combination of the `Y i := Yseq X Δ i` is non-empty in `U`'s
master neighborhood. This is the single fact from which the order-isomorphism `D ≅ᴰ D'` and the
subsystem relation `D' ◁ U` are both assembled. -/
theorem transfer_empty_iff {cs : List (ℕ × Bool)} {n : ℕ} (hn : ∀ p ∈ cs, p.1 < n) :
    {x ∈ Δ | ∀ p ∈ cs, (p.2 = true ↔ x ∈ X p.1)}.Nonempty ↔
      {y ∈ U.master | ∀ p ∈ cs, (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}.Nonempty := by
  have hcore : ∀ δ n, genAtom X Δ δ n = ∅ ↔ genAtom (Yseq split X Δ) U.master δ n = ∅ :=
    fun δ n => (atomU_invariant split X Δ hΔ hsplit n).1 δ
      |>.trans (by rw [atomU_eq_genAtom split X Δ hΔ hsplit])
  have hcore' : ∀ δ n, genAtom (Yseq split X Δ) U.master δ n = ∅ ↔ genAtom X Δ δ n = ∅ :=
    fun δ n => (hcore δ n).symm
  exact ⟨transfer_dir X Δ (Yseq split X Δ) U.master hcore hn,
    transfer_dir (Yseq split X Δ) U.master X Δ hcore' hn⟩

/-- Subset transfer: `X i ⊆ X j` (restricted to the carrier `Δ`) iff `Y i ⊆ Y j` (restricted to
`U.master`). Obtained from `transfer_empty_iff` applied to the two-point constraint list
witnessing `x ∈ X i \ X j`. -/
theorem transfer_subset_iff (i j : ℕ) :
    Δ ∩ X i ⊆ X j ↔ U.master ∩ Yseq split X Δ i ⊆ Yseq split X Δ j := by
  have key := transfer_empty_iff split X Δ hΔ hsplit (cs := [(i, true), (j, false)])
    (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ Δ | ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ x ∈ X p.1)}
      = (Δ ∩ X i) \ X j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master |
      ∀ p ∈ [(i, true), (j, false)], (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}
      = (U.master ∩ Yseq split X Δ i) \ Yseq split X Δ j := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- Intersection transfer: `X i ∩ X j` is empty on `Δ` iff `Y i ∩ Y j` is empty on `U.master`. This
is the key fact ensuring the map `Xᵢ ↦ Yᵢ` respects both inclusions *and* incompatibility, i.e.
that it extends to an order isomorphism between the atomic Boolean combinations, hence to an
order isomorphism of the generated `NeighborhoodSystem`s. -/
theorem transfer_inter_empty_iff (i j : ℕ) :
    Δ ∩ X i ∩ X j = ∅ ↔ U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j = ∅ := by
  have key := transfer_empty_iff split X Δ hΔ hsplit (cs := [(i, true), (j, true)])
    (n := max i j + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl) <;> simp)
  have hLHS : {x ∈ Δ | ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ x ∈ X p.1)}
      = Δ ∩ X i ∩ X j := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master | ∀ p ∈ [(i, true), (j, true)], (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}
      = U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.not_nonempty_iff_eq_empty, ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- Three-term subset transfer: `X i ∩ X j ⊆ X k` (restricted to `Δ`) iff `Y i ∩ Y j ⊆ Y k`
(restricted to `U.master`). Combined with two applications of `transfer_subset_iff` (in the
`m ⊆ i`/`m ⊆ j` direction), this lets an *equation* `X i ∩ X j = X k` on the `D`-side transfer to
the equation `Y i ∩ Y j = Y k` on the `U`-side, and conversely — exactly the fact needed to move
`D`'s own `inter_mem` witnessed-consistency structure across the `Xᵢ ↦ Yᵢ` correspondence. -/
theorem transfer_double_subset_iff (i j k : ℕ) :
    Δ ∩ X i ∩ X j ⊆ X k ↔ U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j ⊆ Yseq split X Δ k := by
  have key := transfer_empty_iff split X Δ hΔ hsplit (cs := [(i, true), (j, true), (k, false)])
    (n := max i (max j k) + 1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;>
          simp [(Nat.le_max_left j k).trans (Nat.le_max_right i (max j k)),
            (Nat.le_max_right j k).trans (Nat.le_max_right i (max j k))])
  have hLHS : {x ∈ Δ | ∀ p ∈ [(i, true), (j, true), (k, false)], (p.2 = true ↔ x ∈ X p.1)}
      = (Δ ∩ X i ∩ X j) \ X k := by
    ext x
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hRHS : {y ∈ U.master |
      ∀ p ∈ [(i, true), (j, true), (k, false)], (p.2 = true ↔ y ∈ Yseq split X Δ p.1)}
      = (U.master ∩ Yseq split X Δ i ∩ Yseq split X Δ j) \ Yseq split X Δ k := by
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hLHS, hRHS] at key
  rw [← Set.sdiff_eq_empty, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    ← Set.not_nonempty_iff_eq_empty, not_iff_not]
  exact key

/-- `Yseq split X Δ n` is always a subset of `U.master`: it is a union of `atomU`-pieces at depth
`n+1`, each of which is `⊆ U.master` by `atomU_subset_master`. -/
theorem Yseq_subset_master (n : ℕ) : Yseq split X Δ n ⊆ U.master :=
  Set.iUnion_subset fun δ' => atomU_subset_master split X Δ hΔ hsplit (extendTrue δ') (n + 1)

/-- **`Yseq split X Δ 0 = U.master` whenever `X 0 = Δ`** (Scott's convention `X₀ = Δ`). Unfolding
one step of the recursion at `n = 0`, both `genAtom X Δ δ 0` and `atomU split X Δ δ 0` are `Δ` and
`U.master` *definitionally*, so splitting against `X 0 = Δ` puts everything into the `"+"`-branch
(the `"-"`-branch `Δ \ Δ = ∅` is forced empty by `split`'s spec), and `I ∪ J = U.master` with
`J = ∅` forces `I = U.master`. -/
theorem Yseq_zero_eq_master (h0 : X 0 = Δ) : Yseq split X Δ 0 = U.master := by
  set δ : ℕ → Bool := extendTrue (fun i : Fin 0 => i.elim0) with hδdef
  have hδ0 : δ 0 = true := by simp [hδdef, extendTrue]
  have hAB : genAtom X Δ δ 0 = ∅ ↔ atomU split X Δ δ 0 = ∅ :=
    ⟨fun h => absurd h hΔ.ne_empty, fun h => absurd h U.master_mem.2.1.ne_empty⟩
  have hBU : atomU split X Δ δ 0 = ∅ ∨ U.mem (atomU split X Δ δ 0) := Or.inr U.master_mem
  have hspec := hsplit hAB hBU (X 0)
  have hJ : (split (genAtom X Δ δ 0) (atomU split X Δ δ 0) (X 0)).2 = ∅ := by
    rw [← hspec.2.2.2.1]
    show genAtom X Δ δ 0 \ X 0 = ∅
    rw [show genAtom X Δ δ 0 = Δ from rfl, h0]
    exact Set.sdiff_self
  have hI : (split (genAtom X Δ δ 0) (atomU split X Δ δ 0) (X 0)).1 = U.master := by
    have hunion := hspec.2.2.2.2.1
    rw [hJ, Set.union_empty] at hunion
    exact hunion
  have hkey : atomU split X Δ δ 1 = U.master := by rw [atomU_succ, hδ0, ite_eq_left rfl]; exact hI
  apply Set.Subset.antisymm (Yseq_subset_master split X Δ hΔ hsplit 0)
  calc U.master = atomU split X Δ δ 1 := hkey.symm
    _ ⊆ Yseq split X Δ 0 := subset_Yseq split X Δ (fun i : Fin 0 => i.elim0)

/-- **Equation transfer.** If `X k = X i ∩ X j` on `D`'s side (with all three sets `⊆ Δ`, as holds
automatically whenever they are genuine `D`-neighbourhoods), then `Y k = Y i ∩ Y j` on `U`'s side,
and conversely. This is assembled from `transfer_subset_iff` (twice, for `Xk ⊆ Xi`/`Xk ⊆ Xj`) and
`transfer_double_subset_iff` (once, for `Xi ∩ Xj ⊆ Xk`). -/
theorem transfer_inter_eq_iff (i j k : ℕ) (hi : X i ⊆ Δ) (_hj : X j ⊆ Δ) (hk : X k ⊆ Δ) :
    X i ∩ X j = X k ↔ Yseq split X Δ i ∩ Yseq split X Δ j = Yseq split X Δ k := by
  have h1 : X k ⊆ X i ↔ Yseq split X Δ k ⊆ Yseq split X Δ i := by
    have := transfer_subset_iff split X Δ hΔ hsplit k i
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right (Yseq_subset_master split X Δ hΔ hsplit k)] at this
  have h2 : X k ⊆ X j ↔ Yseq split X Δ k ⊆ Yseq split X Δ j := by
    have := transfer_subset_iff split X Δ hΔ hsplit k j
    rwa [Set.inter_eq_self_of_subset_right hk,
      Set.inter_eq_self_of_subset_right (Yseq_subset_master split X Δ hΔ hsplit k)] at this
  have h3 : X i ∩ X j ⊆ X k ↔ Yseq split X Δ i ∩ Yseq split X Δ j ⊆ Yseq split X Δ k := by
    have := transfer_double_subset_iff split X Δ hΔ hsplit i j k
    rwa [Set.inter_eq_self_of_subset_right hi,
      Set.inter_eq_self_of_subset_right (Yseq_subset_master split X Δ hΔ hsplit i)] at this
  constructor
  · intro heq
    have hki : X k ⊆ X i := heq ▸ Set.inter_subset_left
    have hkj : X k ⊆ X j := heq ▸ Set.inter_subset_right
    have hijk : X i ∩ X j ⊆ X k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mp hijk) (Set.subset_inter (h1.mp hki) (h2.mp hkj))
  · intro heq
    have hki : Yseq split X Δ k ⊆ Yseq split X Δ i := heq ▸ Set.inter_subset_left
    have hkj : Yseq split X Δ k ⊆ Yseq split X Δ j := heq ▸ Set.inter_subset_right
    have hijk : Yseq split X Δ i ∩ Yseq split X Δ j ⊆ Yseq split X Δ k := heq ▸ subset_rfl
    exact Set.Subset.antisymm (h3.mpr hijk) (Set.subset_inter (h1.mpr hki) (h2.mpr hkj))

/-- `Yseq split X Δ n` is always either empty or a genuine `U`-neighbourhood: it is a finite union
(`Fin n → Bool`) of `atomU` pieces, each of which is `∅` or `U.mem` by `atomU_invariant`. -/
theorem Yseq_empty_or_mem (n : ℕ) : Yseq split X Δ n = ∅ ∨ U.mem (Yseq split X Δ n) := by
  by_cases hne : (Yseq split X Δ n).Nonempty
  · exact Or.inr (U_iUnion_mem
      (fun δ' => (atomU_invariant split X Δ hΔ hsplit (n + 1)).2.1 (extendTrue δ')) hne)
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

/-- If `x ∈ X n` (and `x ∈ Δ`, automatic whenever `X n ⊆ Δ`), then `Yseq split X Δ n` is
non-empty: the canonical sign sequence `δ₀ k := decide (x ∈ X k)` produces a depth-`n` atom
containing `x` (hence non-empty), which `X n` (since `x ∈ X n`) splits into a non-empty
`"+"`-piece that is, by `split_fst_eq_inter_Yseq`, a subset of `Yseq split X Δ n`. -/
theorem Yseq_nonempty_of_mem {n : ℕ} {x : α} (hxΔ : x ∈ Δ) (hxn : x ∈ X n) :
    (Yseq split X Δ n).Nonempty := by
  classical
  set δ0 : ℕ → Bool := fun k => decide (x ∈ X k) with hδ0def
  have hδ0n : δ0 n = true := by show decide (x ∈ X n) = true; rw [decide_eq_true_iff]; exact hxn
  have hxA : x ∈ genAtom X Δ δ0 n := genAtom_self X Δ hxΔ n
  have hAX : x ∈ genAtom X Δ δ0 n ∩ X n := ⟨hxA, hxn⟩
  have hAne : (genAtom X Δ δ0 n ∩ X n).Nonempty := ⟨x, hAX⟩
  obtain ⟨hmatch, hmem, -⟩ := atomU_invariant split X Δ hΔ hsplit n
  have hspec := hsplit (hmatch δ0) (hmem δ0) (X n)
  have hIne : (split (genAtom X Δ δ0 n) (atomU split X Δ δ0 n) (X n)).1 ≠ ∅ :=
    fun h => hAne.ne_empty (hspec.2.2.1.mpr h)
  have hI_eq_atomU : (split (genAtom X Δ δ0 n) (atomU split X Δ δ0 n) (X n)).1 =
      atomU split X Δ δ0 (n + 1) := by rw [atomU_succ, hδ0n, ite_eq_left rfl]
  set δ2 : ℕ → Bool := extendTrue (restrictFin δ0 n) with hδ2def
  have hagree : ∀ i < n + 1, δ2 i = δ0 i := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · exact extendTrue_restrictFin_agree δ0 n i hi'
    · simp [hδ2def, extendTrue, hδ0n]
  have hδ2_eq : atomU split X Δ δ2 (n + 1) = atomU split X Δ δ0 (n + 1) :=
    atomU_congr split X Δ hagree
  have hne2 : (atomU split X Δ δ2 (n + 1)).Nonempty := by
    rw [hδ2_eq, ← hI_eq_atomU]
    exact Set.nonempty_iff_ne_empty.mpr hIne
  exact hne2.mono (subset_Yseq split X Δ (restrictFin δ0 n))
end

section
open NeighborhoodSystem
variable {α : Type*}

open Classical in


open Classical in

theorem splitChoice_isSplitSpec : SplitSpec (α := α) splitChoice := by
  intro A B hAB hBU Xn
  classical
  unfold splitChoice
  rw [dite_eq_left ⟨hAB, hBU⟩]
  exact (exists_split hAB hBU Xn).choose_spec.choose_spec
end

section
open NeighborhoodSystem
variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)

/-- **Scott's `↓(e n)`, reindexed over `ℕ`**: the set of indices `m` whose neighbourhood `e m` sits
below `e n`. This is `D†`'s replacement for `e n` itself. -/
def idxSet (n : ℕ) : Set ℕ := {m | e m ⊆ e n}

end Reencode
end

section
open NeighborhoodSystem
variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)

@[simp] theorem mem_idxSet {m n : ℕ} : m ∈ idxSet e n ↔ e m ⊆ e n := Iff.rfl

end Reencode
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover in
/-- Every enumerated set is a genuine `D`-neighbourhood. -/
theorem D_mem_e (n : ℕ) : D.mem (e n) := (hcover (e n)).mpr ⟨n, rfl⟩

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- **Scott's `Yₙ`, built from the separated reindexing.** Instantiated with the classical
`splitChoice` (this is `Theorem88.lean`'s general, non-effective apparatus). -/
noncomputable abbrev Yidx (n : ℕ) : Set ℚ := Yseq splitChoice (idxSet e) Set.univ n

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover in
theorem e_subset_master (n : ℕ) : e n ⊆ D.master := D.sub_master (D_mem_e D e hcover n)

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)

/-- If `e i ∩ e j = e m` (i.e. `{e i, e j}` is witnessed-consistent, with witness realizing the
intersection exactly as `e m`), then `idxSet e i ∩ idxSet e j = idxSet e m` — a **definitional**
rewriting of the set-builder, needing no transfer at all. -/
theorem idxSet_inter_of_inter_eq {i j m : ℕ} (h : e i ∩ e j = e m) :
    idxSet e i ∩ idxSet e j = idxSet e m := by
  ext k
  show e k ⊆ e i ∧ e k ⊆ e j ↔ e k ⊆ e m
  rw [← Set.subset_inter_iff, h]

end Reencode
end

section
open NeighborhoodSystem
variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)

theorem idxSet_zero_eq_univ {n0 : ℕ} (hsub : ∀ m, e m ⊆ e n0) : idxSet e n0 = Set.univ :=
  Set.eq_univ_of_forall hsub

end Reencode
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover he0 in
theorem idxSet_zero : idxSet e 0 = Set.univ :=
  idxSet_zero_eq_univ e (fun m => he0 ▸ e_subset_master D e hcover m)

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)

/-- Every index belongs to its own `idxSet` (`e n ⊆ e n`) — so `idxSet e n` is always non-empty,
regardless of whether `e n` itself is empty. -/
theorem self_mem_idxSet (n : ℕ) : n ∈ idxSet e n := show e n ⊆ e n from subset_rfl

end Reencode
end

section
open NeighborhoodSystem
variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)

/-- The raw inclusion order on `idxSet`s matches `e`'s own inclusion order — this is the
"separation" property `D†` is built to have. -/
theorem idxSet_subset_iff (i j : ℕ) : idxSet e i ⊆ idxSet e j ↔ e i ⊆ e j :=
  ⟨fun h => h (self_mem_idxSet e i), fun h _ hm => hm.trans h⟩

end Reencode
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- `Δ' := Set.univ` is always non-empty, so the general `Yseq`/transfer apparatus of
`Theorem88.lean` applies to `(idxSet e, Set.univ)` unconditionally — no `∅`-freeness hypothesis on
`D` is ever needed, since we reindexed onto `ℕ` before invoking it (`idxSet_nonempty`). -/
theorem univ_nonempty_nat : (Set.univ : Set ℕ).Nonempty := ⟨0, trivial⟩

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- `Yidx e n` is always `∅` or a genuine `U`-neighbourhood. -/
theorem Yidx_empty_or_mem (n : ℕ) : Yidx e n = ∅ ∨ U.mem (Yidx e n) :=
  Yseq_empty_or_mem splitChoice (idxSet e) Set.univ univ_nonempty_nat splitChoice_isSplitSpec n

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- **`Yidx e n` is always non-empty** (hence, by `Yidx_empty_or_mem`, always a genuine
`U`-neighbourhood): `n` itself witnesses `n ∈ idxSet e n`. -/
theorem Yidx_nonempty (n : ℕ) : (Yidx e n).Nonempty :=
  Yseq_nonempty_of_mem splitChoice (idxSet e) Set.univ univ_nonempty_nat splitChoice_isSplitSpec
    (Set.mem_univ n) (self_mem_idxSet e n)

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

theorem Yidx_mem (n : ℕ) : U.mem (Yidx e n) :=
  (Yidx_empty_or_mem e n).resolve_left (Yidx_nonempty e n).ne_empty

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- `Yidx e n` is always `⊆ U.master`. -/
theorem Yidx_subset_master (n : ℕ) : Yidx e n ⊆ U.master :=
  Yseq_subset_master splitChoice (idxSet e) Set.univ univ_nonempty_nat splitChoice_isSplitSpec n

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover he0 in
/-- `Yidx e 0 = U.master`, since `idxSet e 0 = Set.univ` (Scott's `X₀ = Δ`). -/
theorem Yidx_zero : Yidx e 0 = U.master :=
  Yseq_zero_eq_master splitChoice (idxSet e) Set.univ univ_nonempty_nat splitChoice_isSplitSpec
    (idxSet_zero D e hcover he0)

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- **The order-embedding at the neighbourhood level.** This is where the whole `idxSet`
reindexing pays off: because `idxSet`'s inclusion order matches `e`'s (`idxSet_subset_iff`), the
generic `transfer_subset_iff` (with `Δ' = Set.univ`, so the `Δ' ∩ ·`/`U.master ∩ ·` wrappers are
trivial since `Yidx e i ⊆ U.master` always) yields exactly Scott's matching invariant restricted to
plain inclusion. -/
theorem embed_subset_iff (i j : ℕ) : e i ⊆ e j ↔ Yidx e i ⊆ Yidx e j := by
  rw [← idxSet_subset_iff e i j]
  have := transfer_subset_iff splitChoice (idxSet e) Set.univ univ_nonempty_nat
    splitChoice_isSplitSpec i j
  rwa [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yidx_subset_master e i)] at this

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

theorem embed_eq_iff (i j : ℕ) : e i = e j ↔ Yidx e i = Yidx e j :=
  ⟨fun h => Set.Subset.antisymm ((embed_subset_iff e i j).mp h.subset)
      ((embed_subset_iff e j i).mp h.symm.subset),
    fun h => Set.Subset.antisymm ((embed_subset_iff e i j).mpr h.subset)
      ((embed_subset_iff e j i).mpr h.symm.subset)⟩

end Setup
end

section
open NeighborhoodSystem
variable {α : Type*}

section Subsystem

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover in
/-- **The shared "find a matching index" step.** Given `D.mem (e i ∩ e j)` (however that was
established — a direct witness, or `D`'s own `inter_mem`), `hcover` names it as `e m` for some
`m`, and `transfer_inter_eq_iff` (fed through the `idxSet`-level rewriting
`idxSet_inter_of_inter_eq`) pushes the equation across to `Yidx`. This single lemma drives
`DprimeU`'s `inter_mem`, `DprimeU_subsystem`'s `inter_closed`, and both halves of the element-level
isomorphism below. -/
theorem exists_inter_index_of_dmem {i j : ℕ} (hDij : D.mem (e i ∩ e j)) :
    ∃ m, e i ∩ e j = e m ∧ Yidx e i ∩ Yidx e j = Yidx e m := by
  obtain ⟨m, hm⟩ := (hcover (e i ∩ e j)).mp hDij
  exact ⟨m, hm, (transfer_inter_eq_iff splitChoice (idxSet e) Set.univ univ_nonempty_nat
    splitChoice_isSplitSpec i j m
    (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _)).mp (idxSet_inter_of_inter_eq e hm)⟩

end Subsystem
end

section
open NeighborhoodSystem
variable {α : Type*}

section Subsystem

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- **`D'`**: the neighbourhood system generated by `{Yidx e n ∣ n ∈ ℕ}`. Its `inter_mem` axiom
transfers *directly* from `D`'s own `inter_mem`: a witness `X k ⊆ X i ∩ X j` on the `D'`-side pulls
back (`embed_subset_iff`) to a witness `e k ⊆ e i ∩ e j` on the `D`-side, so `D`'s own axiom
supplies `e m = e i ∩ e j` for some `m`, and `transfer_inter_eq_iff` pushes this equation back
across to `Yidx e i ∩ Yidx e j = Yidx e m`. -/
noncomputable def DprimeU : NeighborhoodSystem ℚ where
  mem Y := ∃ n, Y = Yidx e n
  master := U.master
  master_nonempty := U.master_nonempty
  master_mem := ⟨0, (Yidx_zero D e hcover he0).symm⟩
  sub_master := by rintro Y ⟨n, rfl⟩; exact Yidx_subset_master e n
  inter_mem := by
    rintro X Y Z ⟨i, rfl⟩ ⟨j, rfl⟩ ⟨k, rfl⟩ hZsub
    have h1 : e k ⊆ e i := (embed_subset_iff e k i).mpr (hZsub.trans Set.inter_subset_left)
    have h2 : e k ⊆ e j := (embed_subset_iff e k j).mpr (hZsub.trans Set.inter_subset_right)
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_dmem D e hcover
      (D.inter_mem (D_mem_e D e hcover i) (D_mem_e D e hcover j) (D_mem_e D e hcover k)
        (Set.subset_inter h1 h2))
    exact ⟨m, hYeq⟩

end Subsystem
end

section
open NeighborhoodSystem
variable {α : Type*}

section Subsystem

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover in
/-- **The "unwitnessed" variant**, used exactly when only the raw non-emptiness of `Yidx e i ∩
Yidx e j` is known (not an explicit `D`-side witness): non-emptiness transfers down
(`transfer_inter_empty_iff`) to `idxSet e i ∩ idxSet e j`, any element `k` of which supplies
`e k ⊆ e i ∩ e j`, so `D`'s own `inter_mem` produces `D.mem (e i ∩ e j)` and
`exists_inter_index_of_dmem` finishes. -/
theorem exists_inter_index_of_nonempty {i j : ℕ} (hne : (Yidx e i ∩ Yidx e j).Nonempty) :
    ∃ m, e i ∩ e j = e m ∧ Yidx e i ∩ Yidx e j = Yidx e m := by
  have hne' : (idxSet e i ∩ idxSet e j).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hkey := transfer_inter_empty_iff splitChoice (idxSet e) Set.univ univ_nonempty_nat
      splitChoice_isSplitSpec i j
    rw [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yidx_subset_master e i)] at hkey
    exact hne.ne_empty (hkey.mp hcon)
  obtain ⟨k, hki, hkj⟩ := hne'
  exact exists_inter_index_of_dmem D e hcover
    (D.inter_mem (D_mem_e D e hcover i) (D_mem_e D e hcover j) (D_mem_e D e hcover k)
      (Set.subset_inter hki hkj))

end Subsystem
end

section
open NeighborhoodSystem
variable {α : Type*}

section Subsystem

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

include hcover he0 in
/-- **`D' ◁ U`.** `sub` is `Yidx_mem`; `inter_closed` uses `exists_inter_index_of_nonempty` to find
*some* witnessed-consistent pair on the `D`-side from the mere non-emptiness of `Yidx e i ∩ Yidx e
j` (guaranteed by `U.mem`). -/
theorem DprimeU_subsystem : DprimeU D e hcover he0 ◁ U where
  master_eq := rfl
  sub := by rintro Y ⟨n, rfl⟩; exact Yidx_mem e n
  inter_closed := by
    rintro X Y ⟨i, rfl⟩ ⟨j, rfl⟩ hUmem
    obtain ⟨m, -, hYeq⟩ := exists_inter_index_of_nonempty D e hcover hUmem.2.1
    exact ⟨m, hYeq⟩

end Subsystem
end

section
open NeighborhoodSystem
variable {α : Type*}

section Iso

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- **Pullback**: the `D`-filter `{e n ∣ Yidx e n ∈ y}` induced by a `D'`-filter `y`. -/
def toD (y : (DprimeU D e hcover he0).Element) : D.Element where
  mem S := ∃ n, S = e n ∧ y.mem (Yidx e n)
  sub := fun ⟨n, hn, _⟩ => hn ▸ D_mem_e D e hcover n
  master_mem := ⟨0, he0.symm, by rw [Yidx_zero D e hcover he0]; exact y.master_mem⟩
  inter_mem := by
    rintro S T ⟨i, rfl, hyi⟩ ⟨j, rfl, hyj⟩
    have hD'mem : (DprimeU D e hcover he0).mem (Yidx e i ∩ Yidx e j) := y.sub (y.inter_mem hyi hyj)
    obtain ⟨m, hem, hYeq⟩ := exists_inter_index_of_nonempty D e hcover
      ((DprimeU_subsystem D e hcover he0).sub hD'mem).2.1
    exact ⟨m, hem, hYeq ▸ y.inter_mem hyi hyj⟩
  up_mem := by
    rintro S T ⟨i, rfl, hyi⟩ hDT hST
    obtain ⟨j, rfl⟩ := (hcover T).mp hDT
    have hYij : Yidx e i ⊆ Yidx e j := (embed_subset_iff e i j).mp hST
    exact ⟨j, rfl, y.up_mem hyi ⟨j, rfl⟩ hYij⟩

end Iso
end

section
open NeighborhoodSystem
variable {α : Type*}

section Iso

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- **Pushforward**: the `D'`-filter `{Yidx e n ∣ e n ∈ x}` induced by a `D`-filter `x`. -/
def toDprimeU (x : D.Element) : (DprimeU D e hcover he0).Element where
  mem Y := ∃ n, Y = Yidx e n ∧ x.mem (e n)
  sub := fun ⟨n, hn, _⟩ => ⟨n, hn⟩
  master_mem := ⟨0, (Yidx_zero D e hcover he0).symm, by rw [he0]; exact x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl, hxj⟩
    obtain ⟨m, hem, hYeq⟩ :=
      exists_inter_index_of_dmem D e hcover (x.sub (x.inter_mem hxi hxj))
    exact ⟨m, hYeq, hem ▸ x.inter_mem hxi hxj⟩
  up_mem := by
    rintro X Y ⟨i, rfl, hxi⟩ ⟨j, rfl⟩ hXY
    have heij : e i ⊆ e j := (embed_subset_iff e i j).mpr hXY
    exact ⟨j, rfl, x.up_mem hxi (D_mem_e D e hcover j) heij⟩

end Iso
end

section
open NeighborhoodSystem
variable {α : Type*}

section Iso

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- **The order isomorphism `D.Element ≃o D'.Element`.** `toDprimeU`/`toD` are mutually inverse
(via `embed_eq_iff`, which resolves the ambiguity of *which* index represents a given
neighbourhood) and preserve/reflect `≤` (via `hcover`, which shows every `D`-neighbourhood a
filter can mention is literally some `e n`). -/
noncomputable def domainIso : DomainIso D (DprimeU D e hcover he0) where
  toFun := toDprimeU D e hcover he0
  invFun := toD D e hcover he0
  left_inv x := by
    apply Element.ext
    intro S
    constructor
    · rintro ⟨n, hn, k, hk, hxk⟩
      rw [hn, (embed_eq_iff e n k).mpr hk]
      exact hxk
    · intro hS
      obtain ⟨n, hn⟩ := (hcover S).mp (x.sub hS)
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  right_inv y := by
    apply Element.ext
    intro Y
    constructor
    · rintro ⟨n, hn, k, hk, hyk⟩
      rw [hn, (embed_eq_iff e n k).mp hk]
      exact hyk
    · intro hY
      obtain ⟨n, hn⟩ := y.sub hY
      refine ⟨n, hn, n, rfl, ?_⟩
      rwa [← hn]
  map_rel_iff' := by
    intro x x2
    constructor
    · intro hle S hxS
      obtain ⟨n, hn⟩ := (hcover S).mp (x.sub hxS)
      have hxn : x.mem (e n) := hn ▸ hxS
      obtain ⟨k, hk, hx2k⟩ := hle _ (⟨n, rfl, hxn⟩ : (toDprimeU D e hcover he0 x).mem (Yidx e n))
      rw [hn, (embed_eq_iff e n k).mpr hk]
      exact hx2k
    · intro hle Y hY
      obtain ⟨n, hn, hxn⟩ := hY
      exact ⟨n, hn, hle _ hxn⟩

end Iso
end

section
open NeighborhoodSystem
variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)


theorem idxSet_eq_iff (i j : ℕ) : idxSet e i = idxSet e j ↔ e i = e j :=
  ⟨fun h => Set.Subset.antisymm ((idxSet_subset_iff e i j).mp h.subset)
      ((idxSet_subset_iff e j i).mp h.symm.subset),
    fun h => by rw [idxSet, idxSet, h]⟩

end Reencode
end

section
open NeighborhoodSystem
variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)


theorem idxSet_nonempty (n : ℕ) : (idxSet e n).Nonempty := ⟨n, self_mem_idxSet e n⟩

end Reencode
end

section
open NeighborhoodSystem
variable {α : Type*}

section Iso

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)


/-- **First sentence of Theorem 8.8 (isomorphism half).** `D ≅ᴰ D'`. -/
theorem isomorphic_DprimeU : D ≅ᴰ DprimeU D e hcover he0 := ⟨domainIso D e hcover he0⟩

end Iso
end

section
open NeighborhoodSystem
variable {α : Type*}

end
end DomainTheory.NeighbourhoodSystems
end
