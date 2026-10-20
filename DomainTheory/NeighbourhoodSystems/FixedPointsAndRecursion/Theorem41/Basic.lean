/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises

@[expose] public section

/-!
# Lecture IV (§4) — fixed points and recursion: Theorems 4.1 and 4.2

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture IV,
*Fixed points and recursion*. The heart of the matter is the **Fixed-point Theorem**:

* **Theorem 4.1** — every approximable mapping `f : 𝒟 → 𝒟` has a *least* element `x ∈ |𝒟|` with
  `f(x) = x`. Scott constructs `x = {X ∈ 𝒟 ∣ Δ fⁿ X for some n}`, the family of neighbourhoods
  reachable from the master `Δ` along finitely many `f`-steps. We model the `n`-fold composition
  `fⁿ` by `iterMap f n` (`f⁰ = I_𝒟`, `f^{n+1} = f ∘ fⁿ`) and the fixed point by `fixElement f`.
  The fixed-point equation is `toElementMap_fixElement`; minimality among *pre-fixed* points
  (`f(z) ⊆ z ⟹ x ⊆ z`) is `fixElement_le_of_toElementMap_le`.

* **Theorem 4.2** — the operator `fix : (𝒟 → 𝒟) → 𝒟` is itself approximable. We build it as
  `fixMap V : ApproximableMap (funSpace V V) V` via the extension-from-finite-elements principle
  (Exercise 2.8, `ofMono`), sending the finite element `↑F` to `fix(↑F)` where `↑F = leastMap` is
  the least map of the neighbourhood `F` (here `toApproxMap (↑F)`). The defining computation
  `fixMap.toElementMap φ = fix(toApproxMap φ)` is Scott's equation (∗)
  `fix(f) = ⋃ {fix(↑F) ∣ f ∈ [F]}` (`fixMap_toElementMap`), whose non-trivial half — every
  finite `f`-chain factors through one finite approximant `F ∈ φ` — is `exists_principal_iterMap`.
  Then (i) `fix(f) = f(fix(f))` (`fixMap_fixed`); (ii) `f(x) ⊆ x ⟹ fix(f) ⊆ x` (`fixMap_least`);
  (iii) `fix(f) = ⊔ₙ fⁿ(⊥)` (`fixMap_eq_iSup`, with `iterElem_eq_iterate` giving the faithful
  `⊔ₙ fⁿ(⊥)` form); and uniqueness (`fixMap_unique`).

All *data* constructions (`iterMap`, `fixElement`, `iterElem`, `fixMap`) are **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`); the uniqueness lemma `fixMap_unique` pulls
`Classical.choice` only through the project's `ext_of_toElementMap`, as permitted.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-! ### The iterated map `fⁿ`. -/

/-- **Theorem 4.1 (Scott 1981, PRG-19).** The `n`-fold composition `fⁿ` of an endomap with itself:
`f⁰ = I_𝒟` and `f^{n+1} = f ∘ fⁿ`. -/
def iterMap (f : ApproximableMap V V) : ℕ → ApproximableMap V V
  | 0 => idMap V
  | (n + 1) => f.comp (f.iterMap n)

@[simp] theorem iterMap_zero (f : ApproximableMap V V) : f.iterMap 0 = idMap V := rfl

@[simp] theorem iterMap_succ (f : ApproximableMap V V) (n : ℕ) :
    f.iterMap (n + 1) = f.comp (f.iterMap n) := rfl

/-- Composition is monotone in both arguments. -/
theorem comp_mono {f g a b : ApproximableMap V V} (hfg : f ≤ g) (hab : a ≤ b) :
    f.comp a ≤ g.comp b := by
  intro X Z h
  obtain ⟨Y, hXY, hYZ⟩ := h
  exact ⟨Y, hab X Y hXY, hfg Y Z hYZ⟩

/-- The iterate is monotone in the map: `f ⊑ g ⟹ fⁿ ⊑ gⁿ` (Scott's "`fⁿ ⊆ gⁿ`"). -/
theorem iterMap_mono_map {f g : ApproximableMap V V} (hfg : f ≤ g) (n : ℕ) :
    f.iterMap n ≤ g.iterMap n := by
  induction n with
  | zero => show (idMap V) ≤ (idMap V); exact le_refl _
  | succ k ih => exact comp_mono hfg ih

/-- `f` commutes with its own iterate: `f ∘ fⁿ = fⁿ ∘ f`. Proved by induction using associativity
and the identity laws. -/
theorem iter_comm (f : ApproximableMap V V) (n : ℕ) :
    f.comp (f.iterMap n) = (f.iterMap n).comp f := by
  induction n with
  | zero => rw [show f.iterMap 0 = idMap V from rfl, comp_idMap, idMap_comp]
  | succ n ih =>
    show f.comp (f.comp (f.iterMap n)) = (f.comp (f.iterMap n)).comp f
    rw [comp_assoc, ← ih]

/-- Scott's "a sequence for an `X ∈ x` can always be extended": if `Δ fⁿ X`, then `Δ f^{n+1} X`
(prepend a `Δ`-step, using `Δ f Δ`). -/
theorem rel_master_succ (f : ApproximableMap V V) {n : ℕ} {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap (n + 1)).rel V.master X := by
  have hcomm : f.iterMap (n + 1) = (f.iterMap n).comp f := iter_comm f n
  rw [hcomm]
  exact ⟨V.master, f.master_rel, h⟩

/-- Monotonicity of the reachability relation in the number of steps: `n ≤ m` and `Δ fⁿ X` imply
`Δ fᵐ X`. -/
theorem rel_master_mono (f : ApproximableMap V V) {n m : ℕ} (hnm : n ≤ m) {X : Set α}
    (h : (f.iterMap n).rel V.master X) : (f.iterMap m).rel V.master X := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact rel_master_succ f ih

/-! ### Theorem 4.1 — the least fixed point. -/

/-- **Theorem 4.1 (Scott 1981, PRG-19).** The least fixed point of `f`, Scott's
`x = {X ∈ 𝒟 ∣ Δ fⁿ X for some n}`. The three filter conditions are exactly Scott's: `Δ ∈ x` (the
`n = 0` witness `I_𝒟`); closure under intersection follows from intersectivity (`inter_right`) of
the single iterate `f^{max n m}` reached by extending the shorter chain; upward closure is `mono`. -/
def fixElement (f : ApproximableMap V V) : V.Element where
  mem X := ∃ n, (f.iterMap n).rel V.master X
  sub := fun ⟨n, h⟩ => (f.iterMap n).rel_cod h
  master_mem := ⟨0, show (idMap V).rel V.master V.master from (idMap V).master_rel⟩
  inter_mem := by
    rintro X Y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, ?_⟩
    have hX : (f.iterMap (max n m)).rel V.master X := rel_master_mono f (le_max_left n m) hn
    have hY : (f.iterMap (max n m)).rel V.master Y := rel_master_mono f (le_max_right n m) hm
    exact (f.iterMap (max n m)).inter_right hX hY
  up_mem := by
    rintro X Y ⟨n, hn⟩ hYmem hXY
    exact ⟨n, (f.iterMap n).mono hn subset_rfl hXY V.master_mem hYmem⟩

@[simp] theorem mem_fixElement (f : ApproximableMap V V) {X : Set α} :
    f.fixElement.mem X ↔ ∃ n, (f.iterMap n).rel V.master X := Iff.rfl

/-- The least fixed point is monotone in the map: `f ⊑ g ⟹ fix(f) ⊑ fix(g)` (immediate from
`iterMap_mono_map`; underlies the approximability of `fix` in 4.2). -/
theorem fixElement_mono {f g : ApproximableMap V V} (hfg : f ≤ g) :
    f.fixElement ≤ g.fixElement := by
  rintro X ⟨n, hn⟩
  exact ⟨n, iterMap_mono_map hfg n V.master X hn⟩

/-! ### Theorem 4.2(iii) — the iterates `fⁿ(⊥)`. -/

/-- The `n`-th approximant `fⁿ(⊥)` of the least fixed point. -/
def iterElem (f : ApproximableMap V V) (n : ℕ) : V.Element := (f.iterMap n).toElementMap V.bot

end ApproximableMap

/-! ### Theorem 4.2 — the approximable fixed-point operator `fix`. -/

open ApproximableMap

/-- **Theorem 4.2 (Scott 1981, PRG-19).** The fixed-point operator `fix : (𝒟 → 𝒟) → 𝒟` as an
approximable mapping. Built by the extension principle (Exercise 2.8, `ofMono`): on the finite
element `↑F` it returns `fix(↑F)`, where `↑F = toApproxMap (principal hF)` is the least map of the
neighbourhood `F` (Proposition 3.9). Monotonicity of `↑F ↦ fix(↑F)` is `fixElement_mono` composed
with the order-iso `funSpaceEquiv`. -/
def fixMap (V : NeighborhoodSystem α) : ApproximableMap (funSpace V V) V :=
  ofMono (fun W hW => (toApproxMap ((funSpace V V).principal hW)).fixElement)
    (fun W W' hW hW' hW'W => by
      apply fixElement_mono
      exact (funSpaceEquiv V V).monotone
        (((funSpace V V).principal_le_iff hW hW').mpr hW'W))
end DomainTheory.NeighbourhoodSystems
