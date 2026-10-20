module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.lowerSet
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.upperSet
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise625.mem_lowerSet

@[expose] public section

/-!
# Lecture VI — Exercise 6.25 (Scott 1981, PRG-19): the Galois connection of a projection pair

**Exercise 6.25.** For a projection pair `g : 𝒟 → ℰ` and `h : ℰ → 𝒟` show that for `x ∈ |𝒟|` and
`y ∈ |ℰ|` we have

`g(x) ⊑ y ↔ x ⊑ h(y)`.

Thus conclude

`h(y) = ⊔ {x ∈ |𝒟| ∣ g(x) ⊑ y}`   and   `g(x) = ⊓ {y ∈ |ℰ| ∣ x ⊑ h(y)}`,

so each of the two functions determines the other. Check that the set in the first equation is
directed, and that the set in the second is non-empty. Prove also that `g` maps consistent sets to
consistent sets and **preserves `⊔`** (not just *directed* unions).

## Dictionary to the codebase

Scott's `g` is the injection `i` and his `h` is the projection `j` of Proposition 6.12; we carry
them abstractly in `Subsystem.ProjectionPair 𝒟 ℰ` (fields `inj = g`, `proj = h`) together with the
two defining laws

* `proj_comp_inj : h ∘ g = I_𝒟`  (`P.proj.comp P.inj = idMap 𝒟`), and
* `inj_comp_proj_le : g ∘ h ⊆ I_ℰ`  (`P.inj.comp P.proj ≤ idMap ℰ`).

On *elements* (`toElementMap`) these read `h(g(x)) = x` (`proj_inj_apply`) and `g(h(y)) ⊑ y`
(`inj_proj_apply_le`); everything below is a short consequence of these two facts plus monotonicity
of approximable maps on elements (`toElementMap_mono`).

* `galois` — the adjunction `g(x) ⊑ y ↔ x ⊑ h(y)`.
* `proj_eq_sSup` / `lowerSet_directed` — `h(y) = ⊔ {x ∣ g(x) ⊑ y}`; the set is a down-set of
  `h(y)`, hence directed and bounded by `h(y)`.
* `inj_eq_sInf` — `g(x) = ⊓ {y ∣ x ⊑ h(y)}`; the set is an up-set of `g(x)`, hence non-empty
  (it contains `g(x)`).
* `inj_bounded` — `g` maps bounded ("consistent") sets to bounded sets.
* `inj_sSup` — `g` preserves **all** existing least upper bounds: `g(⊔S) = ⊔ {g(s) ∣ s ∈ S}`.
  This is the hallmark of a lower adjoint and is the substance of the last sentence of the exercise.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`): the `sSup`/`sInf` of
Exercises 1.18/1.27 are the only constructions used and are themselves choice-free.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-! ### First extremal formula: `h(y) = ⊔ {x ∣ g(x) ⊑ y}`. -/



/-! ### Second extremal formula: `g(x) = ⊓ {y ∣ x ⊑ h(y)}`. -/


@[simp] theorem mem_upperSet (P : ProjectionPair D E) {x : D.Element} {y : E.Element} :
    y ∈ P.upperSet x ↔ x ≤ P.proj.toElementMap y := Iff.rfl

/-! ### `g` preserves consistency and all least upper bounds. -/
end Subsystem.ProjectionPair
end DomainTheory.NeighbourhoodSystems
