/-ai
The identity combinator is contained in the universe combinator.

A pair (n, m) in the identity has m in the finite set en. Equation (5.21) puts m in the application of the universe combinator to en, and the application formula says that this application is the graph of x ↦ V(en)(x). The same pair therefore lies in the universe combinator.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_21

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Icomb_subset_Vcomb : Icomb ⊆ Vcomb := by
  intro p hp
  rcases hp with ⟨n, m, rfl, hm⟩
  have : m ∈ funOf Vcomb (e n) := eq_5_21 (e n) hm
  have ha : funOf Vcomb (e n) = graph (fun x => Vapply (e n) x) :=
    Vcomb_app (e n)
  refine ⟨n, m, rfl, ?_⟩
  rwa [ha] at this

end DomainTheory.DataTypesAsLattices
