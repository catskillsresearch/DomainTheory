module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.ComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.inclShuffle
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.swapPair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.reindexInvolutive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.unitPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.inclShuffle
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.swapPair

@[expose] public section

/-!
# Definition 7.1 (Scott 1981, PRG-19, §7) — computable presentations / effectively given domains

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII,
*Computability in effectively given domains*.

Scott's idea: the *finite elements* of `|𝒟|` are the ones initially known, and to know a finite
element is to know how it is **related** to the other finite elements. As finite elements are in
one-one correspondence with neighbourhoods (Definition 1.7), the data reduces to *recursive
calculations with neighbourhoods*. This forces at most a countable infinity of neighbourhoods.

> **Definition 7.1.** A neighbourhood system `𝒟` has a *computable presentation* provided we can
> write `𝒟 = {Xₙ ∣ n ∈ ℕ}`, where the two relations
>
> * (i)  `Xₙ ∩ Xₘ = X_k`, and
> * (ii) `∃ k. X_k ⊆ Xₙ and X_k ⊆ Xₘ`
>
> are recursively decidable (in `n, m, k` and in `n, m` respectively).

**Recursion theory: we roll our own and reject Mathlib here.** "Recursively decidable" is modelled by
`Domain.Recursive.RecDecidable` — the existence of a primitive-recursive `{0,1}`-valued
characteristic function, with tuples coded by `Nat.pair`. We deliberately do **not** use Mathlib's
recursion theory (`ComputablePred` / `Primrec` / `Partrec`): in Mathlib `v4.30.0` essentially all of
its *correctness lemmas* are proved with `grind`/`lia` or the `@[simp]` lemma `Nat.unpair_pair`,
which **open `Classical`**, so they audit with `Classical.choice`. This project's discipline is to
keep constructions choice-free (`⊆ {propext, Quot.sound}`), so we rebuilt the slice of recursion
theory we need (choice-free `Nat.sqrt` correctness, the `Nat.pair`/`unpair` round-trips, and
primitive-recursive `id`/`+`/`*`) in `Domain/Neighborhood/Recursive.lean`. Relation (i) is the
ternary `interEq` predicate (`RecDecidable₃`); relation (ii) is the binary consistency predicate
(`RecDecidable₂`). The enumeration `X` is the only *data* the structure carries (a plain
`ℕ → Set α`), so building a presentation stays choice-free.

The intuitive content (Scott's prose): (i) lets us *locate* the intersection of two neighbourhoods
in the standard list, and (ii) is the *consistency condition* — the necessary and sufficient
condition for the intersection to exist in `𝒟`. Scott immediately remarks the biconditional
`Xₙ ⊆ Xₘ ↔ Xₙ ∩ Xₘ = Xₙ`, which makes the **inclusion** relation decidable from (i); we record this
as `ComputablePresentation.incl_computable`, and equality of neighbourhoods as `eq_computable`.

A neighbourhood system is *effectively given* when it admits such a presentation
(`NeighborhoodSystem.IsEffectivelyGiven`). The one-point system `𝟙` is the sanity inhabitant
(`unitSys_isEffectivelyGiven`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*}


namespace ComputablePresentation

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)


theorem primrec_inclShuffle : Nat.Primrec inclShuffle :=
  Nat.Primrec.pair Nat.Primrec.left (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)


private theorem primrec_swapPair : Nat.Primrec swapPair :=
  Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left

/-- **Scott's biconditional after 7.1.** "The inclusion relation between neighbourhoods is itself
decidable in terms of the indices", because `Xₙ ⊆ Xₘ ↔ Xₙ ∩ Xₘ = Xₙ`. We obtain the decision by
reindexing `(n, m) ↦ (n, m, n)` into relation (i). -/
theorem incl_computable : RecDecidable₂ (fun n m => P.X n ⊆ P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp primrec_inclShuffle)
  simp only [inclShuffle, unpair_pair_fst, unpair_pair_snd]
  exact Set.inter_eq_left.symm

/-- **Equality of neighbourhoods is decidable** from the indices: `Xₙ = Xₘ ↔ Xₙ ⊆ Xₘ ∧ Xₘ ⊆ Xₙ`,
so equality is the conjunction of `incl_computable` with its swap. -/
theorem eq_computable : RecDecidable₂ (fun n m => P.X n = P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_)
    (P.incl_computable.and (P.incl_computable.comp primrec_swapPair))
  simp only [swapPair, unpair_pair_fst, unpair_pair_snd]
  exact Set.Subset.antisymm_iff


end ComputablePresentation


/-! ### Sanity inhabitant: the one-point domain `𝟙` is effectively given. -/

end DomainTheory.NeighbourhoodSystems
