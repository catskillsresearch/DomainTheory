/-ai
If a body lookup is primitive recursive, then the fuel table of that lookup, as a function of the pair of a bound and a fuel, is primitive recursive.

The lookup with its arguments swapped is primitive recursive, hence so is its tabulation, and the zero table of length one more than the bound is primitive recursive in the bound. Packing the bound plus one with the previous table makes the fuel-table step primitive recursive by composition with that tabulation. An auxiliary induction on the fuel shows that primitive recursion from the zero table, stepping by the fuel-table step, equals the fuel table. Primitive recursion with those base and step functions therefore agrees with the fuel table after simplifying the unpaired projections and applying the auxiliary equality.
ai-/
module

public import Mathlib.Data.Nat.Sqrt
import all Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
import all Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
import all Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic

@[expose] public section


namespace Domain.Recursive


set_option maxHeartbeats 1000000 in
/-- `fuelTable bodyLookup · ·` is primitive recursive in `(bound, fuel)` (coded `pair bound
fuel`), whenever `bodyLookup` is. Mirrors `primrec_tabCode`'s `Nat.Primrec.prec` packaging. -/
theorem primrec_fuelTable {bodyLookup : ℕ → ℕ} (hbodyLookup : Nat.Primrec bodyLookup) :
    Nat.Primrec (fun t => fuelTable bodyLookup t.unpair.1 t.unpair.2) := by
  have hgLookup : Nat.Primrec (fun v => bodyLookup (Nat.pair v.unpair.2 v.unpair.1)) :=
    hbodyLookup.comp (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)
  have htab := primrec_tabCode hgLookup
  have hf : Nat.Primrec (fun bound => tabCode (fun _ => 0) (Nat.pair (bound + 1) 0) (bound + 1)) :=
    ((primrec_tabCode (Nat.Primrec.const 0)).comp
      (Nat.Primrec.pair
        (Nat.Primrec.pair (primrec_add₂ Nat.Primrec.id (Nat.Primrec.const 1)) (Nat.Primrec.const 0))
        (primrec_add₂ Nat.Primrec.id (Nat.Primrec.const 1)))).of_eq fun bound => by simp
  have hpack : Nat.Primrec (fun w =>
      Nat.pair (Nat.pair (w.unpair.1 + 1) w.unpair.2.unpair.2) (w.unpair.1 + 1)) :=
    Nat.Primrec.pair
      (Nat.Primrec.pair (primrec_add₂ Nat.Primrec.left (Nat.Primrec.const 1))
        (Nat.Primrec.right.comp Nat.Primrec.right))
      (primrec_add₂ Nat.Primrec.left (Nat.Primrec.const 1))
  have hg : Nat.Primrec (fun w => fuelTableStep bodyLookup w.unpair.1 w.unpair.2.unpair.2) :=
    (htab.comp hpack).of_eq fun w => by simp [fuelTableStep]
  have haux : ∀ bound fuel, Nat.rec (motive := fun _ => ℕ)
      (tabCode (fun _ => 0) (Nat.pair (bound + 1) 0) (bound + 1))
      (fun _ IH => fuelTableStep bodyLookup bound IH) fuel = fuelTable bodyLookup bound fuel := by
    intro bound fuel
    induction fuel with
    | zero => rfl
    | succ fuel ih => show fuelTableStep bodyLookup bound _ = fuelTableStep bodyLookup bound _; rw [ih]
  refine (Nat.Primrec.prec hf hg).of_eq fun t => ?_
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  exact haux t.unpair.1 t.unpair.2

end Domain.Recursive
