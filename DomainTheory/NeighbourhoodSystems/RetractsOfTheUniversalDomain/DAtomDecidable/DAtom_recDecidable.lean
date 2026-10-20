module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtomEmptyChar_eq_one_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.primrec_DAtomEmptyChar

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable (cons : ℕ → ℕ)









variable (incl : ℕ → ℕ)



/-- **Part 5's headline result.** `D`-side atom emptiness (in the `idxSet` sense above) is
recursively decidable in the two constraint-list codes, for any `ComputablePresentation` of `D`.
The primitive-recursive deciders `cons`/`incl` are extracted from `P.cons_computable`/
`P.incl_computable` *inside* this `Prop`-valued goal — an ordinary `Exists`-elimination into a
`Prop`, so this needs no `Classical.choice` beyond what `P` itself already carries. -/
theorem DAtom_recDecidable :
    RecDecidable₂ (fun posC negC => DAtom P (decodeList posC) (decodeList negC) = ∅) := by
  obtain ⟨cons, hconsp, hconss⟩ := P.cons_computable
  obtain ⟨incl, hinclp, hincls⟩ := P.incl_computable
  have hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m := by
    intro n m
    have := hconss (Nat.pair n m)
    simpa only [unpair_pair_fst, unpair_pair_snd] using this.symm
  have hincl : ∀ n m, incl (Nat.pair n m) = 1 ↔ P.X n ⊆ P.X m := by
    intro n m
    have := hincls (Nat.pair n m)
    simpa only [unpair_pair_fst, unpair_pair_snd] using this.symm
  refine ⟨fun t => DAtomEmptyChar P cons incl t.unpair.1 t.unpair.2,
    primrec_DAtomEmptyChar P cons incl hconsp hinclp, fun t => ?_⟩
  exact (DAtomEmptyChar_eq_one_iff P cons incl hcons hincl t.unpair.1 t.unpair.2).symm

end DomainTheory.NeighbourhoodSystems
