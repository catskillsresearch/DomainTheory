module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMapFun

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u


attribute [instance] CLat.str


section Conj

open Set

variable {Y Z W : Type u} [CompleteLattice Y] [CompleteLattice Z] [CompleteLattice W]


theorem conjMapFun_apply (post : ScottMap Y Z) (pre : ScottMap W Y) (f : ScottMap Y Y) (x : W) :
    conjMapFun post pre f x = post (f (pre x)) := rfl

end Conj
end DomainTheory.ContinuousLattice
