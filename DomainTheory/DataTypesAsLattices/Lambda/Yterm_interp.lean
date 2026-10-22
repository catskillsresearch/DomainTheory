
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Yterm_interp : interp Yterm (fun _ => botElem) = Ycomb := by
  simp [Yterm, interp, Ycomb, omegaComb, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
