/-ai
An effective isomorphism of computable presentations is a domain isomorphism of the underlying neighbourhood systems.

Eliminating the witness, the effective isomorphism supplies the domain isomorphism.

If a neighbourhood system has a computable presentation, then the presentation of its iteration is effectively isomorphic to the presentation of the iteration of that iteration.

The packaged isomorphism of an iteration with its double iteration is a witness.

The iteration of a neighbourhood system is isomorphic, as a domain, to the iteration of that iteration.

This is the domain isomorphism underlying the effective isomorphism just obtained.

The numbered name example_718 is the effective isomorphism of an iteration with the iteration of that iteration.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectivelyIsomorphic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.toDomainIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.iterIterEffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_mono
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_inter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2_of_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG_subset_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.exists_inner_bound
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.pair_lt_pair_of_lt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexG_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_comp_Fmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_comp_Gmap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_iterEnum_iter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.masterIdx_iterPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel_enum_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel_enum_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_isComputable

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

/-!
# Exercise 7.18 (Scott 1981, PRG-19, §7) — effective isomorphism; `D^∞ ≅ (D^∞)^∞` is effective

> **EXERCISE 7.18.** Two effectively given systems `D` and `E` are *effectively isomorphic* iff …
> (complete the sentence!). Show that if `D` is effectively given then the isomorphism
> `D^∞ ≅ (D^∞)^∞` is effective.

## Completing the sentence (Definition of *effective isomorphism*)

Scott's Definition 1.9 says `D ≅ E` means there is a one-one, inclusion-preserving correspondence
`|D| ≃o |E|`; Theorem 2.7 shows every such correspondence *is* induced by an approximable map. The
*effective* refinement is the obvious one: the isomorphism, together with its inverse, must be
**computable** in the sense of Definition 7.2. We package this symmetrically as a pair of mutually
inverse computable approximable maps:

* `EffectiveIso P Q` — relative to computable presentations `P` of `D` and `Q` of `E`, a pair
  `toMap : D → E`, `invMap : E → D` of approximable maps, **both computable** (`IsComputableMap`),
  that are mutually inverse (`invMap ∘ toMap = I_D` and `toMap ∘ invMap = I_E`).
* `EffectivelyIsomorphic P Q := Nonempty (EffectiveIso P Q)`.

Every effective isomorphism is in particular a domain isomorphism (`EffectiveIso.toDomainIso`,
`EffectivelyIsomorphic.isomorphic`), so this tightens Scott's `≅` (and, via Exercise 7.13's
`reconstruct_isomorphic`, tightens its "essentially the same").

## `D^∞ ≅ (D^∞)^∞` is effective

`D^∞ = iterSys V` (Exercise 3.16) has token type `ℕ × α` and elements the infinite sequences
`⟨x_k⟩` of `|D|`-elements (`iterSeqEquiv`). `(D^∞)^∞ = iterSys (iterSys V)` has token type
`ℕ × (ℕ × α)` and elements the *double* sequences `⟨⟨x_{i,j}⟩_j⟩_i`. The isomorphism is the index
reindexing along `Nat.pair`/`Nat.unpair`: `x_k ↔ x_{(unpair k).1,(unpair k).2}`, i.e.
`x_{i,j} = x_{pair i j}`.

We realise the two directions as explicit approximable maps with clean neighbourhood relations
(`Fmap`, `Gmap`), where the *double-indexed fiber* of a `(D^∞)^∞`-neighbourhood `S` is
`fiber2 S i j = fiber (fiber S i) j`:

* `Fmap.rel W S ↔ ∀ i j, fiber W (pair i j) ⊆ fiber2 S i j`;
* `Gmap.rel S W ↔ ∀ k, fiber2 S (unpair k).1 (unpair k).2 ⊆ fiber W k`.

They are mutually inverse (`Gmap.comp Fmap = I`, `Fmap.comp Gmap = I`), proved directly on the
relations using the reindexing constructions `reindexF`/`reindexG`. Each is **recursively decidable**
(hence computable) over `iterPresentation P` / `iterPresentation (iterPresentation P)`: the relation
on codes reduces to a *bounded* check of `incl_computable` over the coordinates `(i,j)` (resp. `k`)
that the codes actually constrain (everything beyond the coded fiber lengths is `Δ`, so trivially
satisfied). The whole development is choice-free (`⊆ {propext, Quot.sound}`): the one place a finite
maximum is needed (the cofinite bound of `reindexG`) is obtained by a `Prop`-level induction, not by
choosing witnesses.
-/

namespace DomainTheory.NeighbourhoodSystems
namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

/-! ## Part 1 — the definition of *effective isomorphism* -/



namespace EffectiveIso

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
  {P : ComputablePresentation V} {Q : ComputablePresentation W}


end EffectiveIso

/-- **Exercise 7.18 — effective isomorphism implies domain isomorphism.** -/
theorem EffectivelyIsomorphic.isomorphic {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {P : ComputablePresentation V} {Q : ComputablePresentation W}
    (h : EffectivelyIsomorphic P Q) : V ≅ᴰ W :=
  h.elim fun e => ⟨e.toDomainIso⟩

/-! ## Part 2 — `D^∞ ≅ (D^∞)^∞` is effective.

Throughout, `V : NeighborhoodSystem α`; `D^∞ = iterSys V` over `ℕ × α`, and
`(D^∞)^∞ = iterSys (iterSys V)` over `ℕ × (ℕ × α)`. -/

variable {V : NeighborhoodSystem α}







/-! ### The reindexing constructions. -/








/-! #### A choice-free uniform inner bound for `(D^∞)^∞`-neighbourhoods.

`reindexG S` is cofinite-`Δ` because the active coordinates `(i, j)` are finite (`i` below the outer
bound, `j` below each inner bound). We obtain a uniform inner bound `M` over `i < n` by `Prop`-level
induction — no witnesses are *chosen*, so this stays choice-free. -/




/-! ### The two approximable maps. -/





/-! ### `F` and `G` are mutually inverse. -/



/-! ### Computability of `F` and `G`.

We work over `iterPresentation P` (for `D^∞`) and `iterPresentation (iterPresentation P)` (for
`(D^∞)^∞`). The double-indexed fiber of the `(D^∞)^∞`-enumeration reads off as a doubly-indexed
`iterIdx`: -/

variable (P : ComputablePresentation V)



variable {P}





/-! ### Packaging: the effective isomorphism. -/


/-- **Exercise 7.18 (Scott 1981, PRG-19).** If `D` is effectively given then `D^∞ ≅ (D^∞)^∞` is
effective. -/
theorem iterSys_effectivelyIsomorphic_iterIter (P : ComputablePresentation V) :
    EffectivelyIsomorphic (iterPresentation P) (iterPresentation (iterPresentation P)) :=
  ⟨iterIterEffectiveIso P⟩

/-- As a corollary, `D^∞ ≅ (D^∞)^∞` as domains (Scott's underlying isomorphism). -/
theorem iterSys_isomorphic_iterIter (P : ComputablePresentation V) :
    iterSys V ≅ᴰ iterSys (iterSys V) :=
  (iterSys_effectivelyIsomorphic_iterIter P).isomorphic

end Exercise718
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems.Exercise718

set_option linter.unusedVariables false

theorem example_718.{u_1} : ∀ {α : Type u_1} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V),
  @DomainTheory.NeighbourhoodSystems.Exercise718.EffectivelyIsomorphic (Prod Nat α) (Prod Nat (Prod Nat α))
    (@DomainTheory.NeighbourhoodSystems.iterSys α V)
    (@DomainTheory.NeighbourhoodSystems.iterSys (Prod Nat α) (@DomainTheory.NeighbourhoodSystems.iterSys α V))
    (@DomainTheory.NeighbourhoodSystems.iterPresentation α V P)
    (@DomainTheory.NeighbourhoodSystems.iterPresentation (Prod Nat α) (@DomainTheory.NeighbourhoodSystems.iterSys α V)
      (@DomainTheory.NeighbourhoodSystems.iterPresentation α V P)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise718.iterSys_effectivelyIsomorphic_iterIter

end DomainTheory.NeighbourhoodSystems.Exercise718
