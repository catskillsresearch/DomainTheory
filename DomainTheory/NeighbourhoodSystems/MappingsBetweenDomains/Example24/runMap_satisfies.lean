/-ai
The run map satisfies the four run equations: prepending a zero commutes with the map, prepending two ones leaves the value unchanged, prepending one and then zero emits a zero and then the input, and the principal element of a single one is sent to bottom.

Each clause compares elements by the neighbourhoods they contain. For a leading zero, the input and output shift formulas reduce both sides to a cone of the remaining element, and the output of a leading zero matches the inclusions. For two leading ones, the input shift formula does the same, using that a second one leaves the output unchanged. For one followed by zero, the input shift formula turns a witness into a cone whose output is zero followed by the tail, which is membership in the shifted element, and a membership there unpacks to such a cone. For the single one above bottom, a cone of bottom is empty and the output is empty; rewriting the empty cone to the whole set, containment forces the neighbourhood to be the whole set, which is membership in bottom. The converse rebuilds the empty-cone witness from that membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_append_false
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_append_trueTrue
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.out_append_trueFalse
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.runMap_toElementMap_sigmaElt
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example24.sigmaElt_runMap_toElementMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`runMap` satisfies its own defining equations.** `zero`/`oneOne`/`oneZero` are direct
instances of the two "shift formulas" (`runMap_toElementMap_sigmaElt` on the input side,
`sigmaElt_runMap_toElementMap` on the output side), using that the output of a leading `0`
(resp. `11`, `10`) is fixed by `out_append_false`/`out_append_trueTrue`/`out_append_trueFalse`
regardless of the tail. `one` reads off the unique cone (`Λ`) that `⊥` sits in
(`bot_mem_cone_iff`), where `out [true] = []`. -/
theorem runMap_satisfies : SatisfiesRunEquations runMap where
  zero x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt, sigmaElt_runMap_toElementMap]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_false] at hsub⟩
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_false]⟩
  oneOne x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt, runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_trueTrue] at hsub⟩
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [← out_append_trueTrue] at hsub⟩
  oneZero x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      rw [out_append_trueFalse] at hsub
      exact ⟨hYmem, cone τ, hτ, by rw [prepend_cone]; exact hsub⟩
    · rintro ⟨hYmem, X, hX, hsub⟩
      obtain ⟨τ, rfl⟩ := x.sub hX
      rw [prepend_cone] at hsub
      exact ⟨τ, hX, hYmem, by rwa [out_append_trueFalse]⟩
  one := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      obtain rfl : τ = [] := bot_mem_cone_iff.mp hτ
      rw [show out ([true] ++ ([] : Str)) = ([] : Str) from rfl, cone_nil] at hsub
      rw [mem_bot]
      exact Set.eq_univ_of_univ_subset hsub
    · intro hY
      rw [mem_bot] at hY
      refine ⟨[], bot_mem_cone_iff.mpr rfl, hY ▸ B.master_mem, ?_⟩
      rw [show out ([true] ++ ([] : Str)) = ([] : Str) from rfl, cone_nil, hY, B_master]

end DomainTheory.NeighbourhoodSystems.Example24
