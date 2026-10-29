module

public import DomainTheory.ContinuousLattice.ContinuousLattices.IdempotentFixedPoint.supremumSet

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

variable {L : Type*} [CompleteLattice L] {e : L → L}

namespace IdempotentFixedPoint

@[reducible] noncomputable def completeLattice (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e) :
    CompleteLattice (IdempotentFixedPoint e) :=
  letI := supremumSet hidem
  completeLatticeOfSup (IdempotentFixedPoint e) (supremumSet.isLUB hidem hmono)

namespace completeLattice

theorem coe (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e)
    (S : Set (IdempotentFixedPoint e)) :
    letI := IdempotentFixedPoint.completeLattice hidem hmono
    ((sSup S : IdempotentFixedPoint e) : L) = e (sSup (Subtype.val '' S)) := rfl

end completeLattice

end IdempotentFixedPoint

end DomainTheory.ContinuousLattice
