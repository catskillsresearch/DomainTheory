module

public import DomainTheory.ContinuousLattice.InverseLimits.InverseLimit
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]

variable (P : ∀ n, ContinuousLatticeProjection (D n) (D (n + 1)))

abbrev inverseLimitLE (x y : InverseLimit D P) : Prop :=
  ∀ n,
    @LE.le (D n)
      (ChainCompletePartialOrder.instOfCompleteLattice
        (α := D n)).toPartialOrder.toPreorder.toLE
      (x.1 n) (y.1 n)

namespace inverseLimitLE

theorem refl (x : InverseLimit D P) :
    inverseLimitLE D P x x :=
  fun n => le_refl (x.1 n)

theorem trans (x y z : InverseLimit D P)
    (hxy : inverseLimitLE D P x y) (hyz : inverseLimitLE D P y z) :
    inverseLimitLE D P x z :=
  fun n => le_trans (hxy n) (hyz n)

theorem antisymm (x y : InverseLimit D P)
    (hxy : inverseLimitLE D P x y) (hyx : inverseLimitLE D P y x) :
    x = y :=
  Subtype.ext (funext fun n => le_antisymm (hxy n) (hyx n))

end inverseLimitLE

end InverseLimit

end DomainTheory.ContinuousLattice
