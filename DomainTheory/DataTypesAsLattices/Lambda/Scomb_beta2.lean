/-ai
A second application of S, at g, is the graph of the map sending x to the application of f at x applied to g at x.

Rewrite by the first beta law for S, then beta-reduce, using Scott continuity of the middle map at f.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_mid_cont
public import DomainTheory.DataTypesAsLattices.Lambda.Scomb_beta

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

































theorem Scomb_beta2 (f g : Pomega) :
    funOf (funOf Scomb f) g =
      graph (fun x => funOf (funOf f x) (funOf g x)) := by
  rw [Scomb_beta]
  exact beta (Scomb_mid_cont f) g

end DomainTheory.DataTypesAsLattices
