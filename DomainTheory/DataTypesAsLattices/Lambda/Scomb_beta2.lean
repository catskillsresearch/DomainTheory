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
