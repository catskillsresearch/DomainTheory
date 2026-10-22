module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Prepending the empty prefix fixes every element.** `Λx = x` — the identity case of
`sigmaElt`, matching `prepend_nil` on neighbourhoods. -/
theorem sigmaElt_nil (x : B.Element) : sigmaElt [] x = x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    rw [prepend_nil] at hsub
    exact x.up_mem hX hY hsub
  · intro hY
    exact ⟨x.sub hY, Y, hY, by rw [prepend_nil]⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
