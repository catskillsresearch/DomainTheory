module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.ComputableBisection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e.negIdxFromBisection

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_emptyDiffDec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.primrec_emptyInterDec
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

namespace ComputableBisection

variable {α γ : Type*} {V : NeighborhoodSystem α} {W : NeighborhoodSystem γ}
  (P : ComputablePresentation V) (hDiff : IsComputableDiff P)
  {Q : ComputablePresentation W} (B : ComputableBisection Q) (hWnomin : W.NoMinimal)

theorem primrec_negIdxFromBisection :
    Nat.Primrec (fun t => negIdxFromBisection P hDiff B
      t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hnk : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 t.unpair.2.unpair.2) := hn.pair hk
  have hinter : Nat.Primrec
      (fun t : ℕ => emptyInterDec P (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec_emptyInterDec P).comp hnk
  have hdiffD : Nat.Primrec
      (fun t : ℕ => emptyDiffDec P hDiff (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) :=
    (primrec_emptyDiffDec P hDiff).comp hnk
  have hright : Nat.Primrec (fun t : ℕ => B.right t.unpair.2.unpair.1) := B.right_primrec.comp hm
  have hinner : Nat.Primrec (fun t : ℕ => selectFn
      (emptyDiffDec P hDiff (Nat.pair t.unpair.1 t.unpair.2.unpair.2)) t.unpair.2.unpair.1
      (B.right t.unpair.2.unpair.1)) :=
    primrec_selectFn hdiffD hm hright
  exact (primrec_selectFn hinter hm hinner).of_eq fun _ => rfl

end ComputableBisection

end DomainTheory.NeighbourhoodSystems
