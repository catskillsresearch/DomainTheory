/-ai
A combinator that lies in every function space A → A equals the combinator I.

The empty equivalence supplies the graph equation. Graph comparison with I reduces the claim to values at an argument a. The closure theorem, applied to the singleton equivalence of a, shows that the value lies in that singleton, hence equals a, which is the application law for I.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.singletonE_mem
public import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_1
public import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
public import DomainTheory.DataTypesAsLattices.Functionality.Icomb_isGraph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem theorem_7_3_I_unique (i : Pomega)
    (hi : ∀ A, (arrowE A A).mem i) : i = Icomb := by
  have hgraph : i = graph (fun x => funOf i x) := (hi emptyE).1
  apply graph_funOf_ext hgraph Icomb_isGraph
  intro a
  have ha : (singletonE a).mem (funOf i a) :=
    (theorem_7_1 (singletonE a) (singletonE a)).2.1 (hi (singletonE a))
      ((singletonE_mem a a).mpr rfl)
  simpa [Icomb_app, singletonE_mem] using ha

end DomainTheory.DataTypesAsLattices
