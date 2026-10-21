/-ai
A nonempty recursively enumerable relation on pairs of natural numbers holds of n and m if and only if some index is sent to n by one primitive-recursive function and to m by another.

View the relation as a recursively enumerable set of paired codes. The pair of the given witnesses lies in that set, so a primitive-recursive function enumerates it. Take the two components of each value; both component maps are primitive recursive. A pair lies in the relation exactly when its code lies in the range, and splitting that code into components and reassembling them matches the two component equations with equality of the code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise714

open NeighborhoodSystem Domain.Recursive DomainTheory.NeighbourhoodSystems


/-- **A non-empty recursively enumerable relation is enumerated by a pair of primitive recursive
functions** (Scott's `f = {(X_{s(i)}, Y_{r(i)}) ∣ i ∈ ℕ}`). Apply `repred_exists_primrec_range` to
the `Nat.pair`-coded relation and split the resulting range function into its two coordinates. -/
theorem repred₂_exists_primrec_enum {p : ℕ → ℕ → Prop} (hp : REPred₂ p) {a b : ℕ}
    (hab : p a b) :
    ∃ s r : ℕ → ℕ, Nat.Primrec s ∧ Nat.Primrec r ∧
      ∀ n m, p n m ↔ ∃ i, s i = n ∧ r i = m := by
  have hp' : REPred (fun t => p t.unpair.1 t.unpair.2) := hp
  have hwit : (fun t => p t.unpair.1 t.unpair.2) (Nat.pair a b) := by
    simp only [unpair_pair_fst, unpair_pair_snd]; exact hab
  obtain ⟨pf, hpf, hspec⟩ := repred_exists_primrec_range hp' hwit
  refine ⟨fun i => (pf i).unpair.1, fun i => (pf i).unpair.2,
    Nat.Primrec.left.comp hpf, Nat.Primrec.right.comp hpf, fun n m => ?_⟩
  have h := hspec (Nat.pair n m)
  simp only [unpair_pair_fst, unpair_pair_snd] at h
  rw [h]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_, ?_⟩
    · show (pf i).unpair.1 = n; rw [hi, unpair_pair_fst]
    · show (pf i).unpair.2 = m; rw [hi, unpair_pair_snd]
  · rintro ⟨i, hs, hr⟩
    refine ⟨i, ?_⟩
    change (pf i).unpair.1 = n at hs
    change (pf i).unpair.2 = m at hr
    rw [← hs, ← hr]; exact (pair_unpair _).symm

end DomainTheory.NeighbourhoodSystems.Exercise714
