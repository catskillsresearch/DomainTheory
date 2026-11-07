module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fixComputable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive ApproximableMap

/-- Scott's Theorem 7.6: the fixpoint map is computable. -/
theorem theorem_76 :
    ∀ {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
      (gN incl eq : ℕ → ℕ)
      (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P P (decodeList c))
        : Set (ApproximableMap V V)).Nonempty) (hgNp : Nat.Primrec gN)
      (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl)
      (heq : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2) (heqp : Nat.Primrec eq),
      ComputableMap
        (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp) P
        (fixMap V) :=
  @fixMap_isComputable
end

end DomainTheory.NeighbourhoodSystems
