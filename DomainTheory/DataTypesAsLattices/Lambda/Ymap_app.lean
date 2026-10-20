module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.fix_param_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















































theorem Ymap_app {g : Pomega → Pomega → Pomega}
    (hgx : ∀ y, IsScottContinuous (fun x => g x y))
    (hgy : ∀ x, IsScottContinuous (fun y => g x y)) (x : Pomega) :
    funOf (Ymap g) x = fix (g x) :=
  beta (fix_param_isScottContinuous hgx hgy) x

end DomainTheory.DataTypesAsLattices
