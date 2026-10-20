module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel.primrec_isPeriodicMask

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive










theorem primrec_minLevel : Nat.Primrec (fun t => minLevel t.unpair.1 t.unpair.2) := by
  -- `w` is shaped `pair (pair k m) (pair i ih)`, matching `Nat.Primrec.prec`'s own convention
  -- (parameter `pair k m`, recursion variable `i`, accumulator `ih`).
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have hm : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hi : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hih : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hsub : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 - w.unpair.2.unpair.2) :=
    primrec_sub₂ hi hih
  have hpm : Nat.Primrec (fun w : ℕ => isPeriodicMask w.unpair.1.unpair.1 w.unpair.2.unpair.1
      w.unpair.1.unpair.2) :=
    (primrec_isPeriodicMask.comp (hk.pair (hi.pair hm))).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hsucc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1 + 1) := Nat.Primrec.succ.comp hi
  have hGfn : Nat.Primrec (fun w =>
      selectFn (isZero (w.unpair.2.unpair.1 - w.unpair.2.unpair.2))
        (selectFn (isPeriodicMask w.unpair.1.unpair.1 w.unpair.2.unpair.1 w.unpair.1.unpair.2)
          w.unpair.2.unpair.1 (w.unpair.2.unpair.1 + 1))
        w.unpair.2.unpair.2) :=
    primrec_selectFn (primrec_isZero.comp hsub) (primrec_selectFn hpm hi hsucc) hih
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 0) hGfn
  have hpack : Nat.Primrec (fun t : ℕ => Nat.pair t (t.unpair.1 + 1)) :=
    Nat.Primrec.id.pair (Nat.Primrec.succ.comp Nat.Primrec.left)
  refine (hprec.comp hpack).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  rfl

end DomainTheory.NeighbourhoodSystems
