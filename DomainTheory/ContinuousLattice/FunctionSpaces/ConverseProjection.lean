module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.ConverseRetraction

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

open Set

variable {D : Type u} {D' : Type v}
variable [CompleteLattice D] [CompleteLattice D']

noncomputable def ConverseProjection (i : D → D')
    (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (hinj : Function.Injective i)
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : ContinuousLattice D) :
    ContinuousLatticeProjection D D' where
  incl := ⟨i, PreservesDirectedSup.continuous_of (fun _ _ _ => hi _)⟩
  retr := ⟨ConverseRetraction.ConverseRetraction i, PreservesDirectedSup.continuous_of
    (ConverseRetraction.preservesDirectedSup i hi hwb hD)⟩
  retr_incl := fun d => ConverseRetraction.converseRetr_incl i hi hinj d
  incl_retr_le := fun x' => ConverseRetraction.incl_converseRetr_le i hi x'

end DomainTheory.ContinuousLattice
