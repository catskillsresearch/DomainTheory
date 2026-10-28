
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Vapply
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_21
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Icomb_subset_Vcomb : Icomb ⊆ Vcomb := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have : m ∈ funOf Vcomb (e n) := eq_5_21 (e n) hm
  have ha : funOf Vcomb (e n) = graph (fun x => Vapply (e n) x) :=
    Vcomb.app (e n)
  refine ⟨n, m, rfl, ?_⟩
  rwa [ha] at this

end DomainTheory.DataTypesAsLattices
