/-ai
This file gathers and re-exports the two-point neighbourhood system, the check and fade combinators, the retraction built from an element, the fixed-point elements and their order, and the order isomorphism between the two-point system and the fixed-point set, together with the membership and comparison lemmas used to construct them.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fade₂
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fade
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixIso
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fin2_zero_subset_zero_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fin2_zero_ne_zero_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_master_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.exists_mem_ne_master_of_ne_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_toElementMap_check
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.toElementMap_ofMap₂_pair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_toElementMap₂_fade
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_toElementMap_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO_ne_bot_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.toElementMap_a_fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_toElementMap_fixOfO
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO_check_toElementMap
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_le_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fixOfO_mono

@[expose] public section

/-!
# Lecture VIII — Examples 8.4 (Scott 1981, PRG-19): `check`/`fade` and the two-point retraction

Scott's **EXAMPLES 8.4** is really three worked examples built from the *same* pair of
combinators `check`/`fade`. This file formalizes the first, headline example, labelled
**Example 8.4(a)** in `arxiv.md`; the other two (`strict`/`smash` as projections, Example 8.4(b))
are a separate, larger effort building on the same `check`/`fade` machinery — see the strategy note
on the 8.4(b) row of `arxiv.md`.

**Example 8.4(a).** If a system `D` is not trivial (there is some `u ∈ |D|` with `u ≠ ⊥`), then the
two-element system `O = {{0},{0,1}}` arises from a retraction on `D`. Scott's construction:

* `check : D → O` by `X check Y ↔ Y = {0,1} ∨ X ≠ Δ`. So `check(x) = ⊥_O` iff `x = ⊥_D`.
* `fade : O × D → D` (left to the reader) by `fade(t, x) = ⊥_D` if `t = ⊥_O`, else `x`.
* Fix any `u ≠ ⊥_D` and set `a(x) = fade(check(x), u)`. Then `a` is a retraction (not generally a
  projection) and the range of `a` is isomorphic to `O`.

## Formalization strategy

* `O` is built directly as a `NeighborhoodSystem (Fin 2)` with `mem = {{0},{0,1}}`.
* `check` is built as a literal `ApproximableMap D O` from Scott's formula (a `Prop`-valued
  relation, no case-splitting/decidability needed for the *definition* itself).
* `fade` is built via the two-variable bridge `ApproximableMap₂`/`ofMap₂` (Theorem 3.5): the
  two-variable relation `fade₂ : ApproximableMap₂ O D D` is `Z = Δ_D ∨ (X = {0} ∧ Y ⊆ Z)` — the
  disjunct `Z = Δ_D` is always a safe ("least informative") output regardless of the `O`-input,
  and `X = {0} ∧ Y ⊆ Z` is the "pass `x` through" branch.
* `a := fade.comp (paired check (constMap D u))` is Scott's literal composite. Unfolding it via
  `toElementMap_comp`/`toElementMap_paired`/`toElementMap_constMap`/the `ApproximableMap₂` bridge
  gives the clean closed form `mem_toElementMap_a`: `a(x) ∋ Z ↔ Z = Δ_D ∨ (x ≠ ⊥_D ∧ u ∋ Z)` — i.e.
  literally "`a(x) = ⊥_D` if `x = ⊥_D`, else `u`" (`a_bot`, `a_of_ne_bot`).
* From the closed form, `IsRetraction a` is immediate case analysis (`x = ⊥` is fixed at `⊥`;
  `x ≠ ⊥` lands on `u ≠ ⊥`, itself fixed).
* The fixed-point set is exactly `{⊥_D, u}`. Rather than characterizing it abstractly, the
  isomorphism to `O` is built *directly* and choice-freely from the same closed-form data:
  `fixOfO t` (for `t : O.Element`) is the filter `Z ↦ Z = Δ_D ∨ (t ∋ {0} ∧ u ∋ Z)` (the "plug `t`'s
  informativeness into `a`'s formula" filter — a genuine `Element`, no `if`/`Classical.choice` in
  the *data*), and `invOfFix y := check.toElementMap y`. The round-trip/order-preservation facts
  needed for the `OrderIso` are proved from the closed forms; a few individual `Prop`-level steps
  use classical case splits (`by_contra`/`push_neg`), consistent with the project's choice
  discipline (data stays choice-free; supporting propositions may use `Classical.choice`, flagged
  in the axiom audit recorded in `HANDOFF.md`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

/-! ### The two-point domain `O = {{0},{0,1}}`. -/


/-! ### `check : D → O` (Scott's `X check Y ↔ Y = {0,1} ∨ X ≠ Δ`). -/

variable {α : Type*} {D : NeighborhoodSystem α}


/-! ### `fade : O × D → D` (Scott leaves the formula to the reader). -/


/-! ### `a(x) = fade(check(x), u)`: the retraction. -/

variable (u : D.Element) (hu : u ≠ D.bot)


/-! ### The range of `a` is isomorphic to `O`. -/


end DomainTheory.NeighbourhoodSystems
